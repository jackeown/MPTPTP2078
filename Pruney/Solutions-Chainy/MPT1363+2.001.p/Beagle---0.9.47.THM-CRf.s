%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:53 EST 2020

% Result     : Theorem 6.32s
% Output     : CNFRefutation 6.49s
% Verified   : 
% Statistics : Number of formulae       :  248 (1894 expanded)
%              Number of leaves         :   29 ( 673 expanded)
%              Depth                    :   14
%              Number of atoms          :  728 (7359 expanded)
%              Number of equality atoms :  103 ( 582 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_compts_1(B,A)
                    & r1_tarski(C,B)
                    & v4_pre_topc(C,A) )
                 => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( B = k1_xboole_0
             => ( v2_compts_1(B,A)
              <=> v1_compts_1(k1_pre_topc(A,B)) ) )
            & ( v2_pre_topc(A)
             => ( B = k1_xboole_0
                | ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C))))
                 => ( ( B = D
                      & r1_tarski(B,C) )
                   => k1_pre_topc(A,B) = k1_pre_topc(k1_pre_topc(A,C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

tff(c_30,plain,(
    ~ v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4265,plain,(
    ! [B_298,A_299] :
      ( v2_compts_1(B_298,A_299)
      | ~ v1_compts_1(k1_pre_topc(A_299,B_298))
      | k1_xboole_0 = B_298
      | ~ v2_pre_topc(A_299)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4278,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_4265])).

tff(c_4289,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_4278])).

tff(c_4290,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4289])).

tff(c_4294,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4290])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_79,plain,(
    ! [A_64,B_65] :
      ( u1_struct_0(k1_pre_topc(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_96,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_89])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5137,plain,(
    ! [A_348,C_349,D_350] :
      ( k1_pre_topc(k1_pre_topc(A_348,C_349),D_350) = k1_pre_topc(A_348,D_350)
      | ~ r1_tarski(D_350,C_349)
      | ~ m1_subset_1(D_350,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_348,C_349))))
      | ~ m1_subset_1(C_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ m1_subset_1(D_350,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5592,plain,(
    ! [A_370,C_371,A_372] :
      ( k1_pre_topc(k1_pre_topc(A_370,C_371),A_372) = k1_pre_topc(A_370,A_372)
      | ~ r1_tarski(A_372,C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ m1_subset_1(A_372,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370)
      | ~ r1_tarski(A_372,u1_struct_0(k1_pre_topc(A_370,C_371))) ) ),
    inference(resolution,[status(thm)],[c_4,c_5137])).

tff(c_5607,plain,(
    ! [A_372] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_372) = k1_pre_topc('#skF_1',A_372)
      | ~ r1_tarski(A_372,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(A_372,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_372,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_5592])).

tff(c_5623,plain,(
    ! [A_373] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_373) = k1_pre_topc('#skF_1',A_373)
      | ~ m1_subset_1(A_373,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_373,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_5607])).

tff(c_5630,plain,
    ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_5623])).

tff(c_5637,plain,(
    k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5630])).

tff(c_155,plain,(
    ! [A_70,B_71] :
      ( m1_pre_topc(k1_pre_topc(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_166,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_155])).

tff(c_173,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( l1_pre_topc(B_10)
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_173,c_12])).

tff(c_208,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_202])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v2_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,
    ( v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_205,plain,(
    v2_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_199])).

tff(c_2106,plain,(
    ! [A_188,B_189] :
      ( v1_compts_1(k1_pre_topc(A_188,B_189))
      | ~ v2_compts_1(B_189,A_188)
      | k1_xboole_0 = B_189
      | ~ v2_pre_topc(A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5489,plain,(
    ! [A_359,A_360] :
      ( v1_compts_1(k1_pre_topc(A_359,A_360))
      | ~ v2_compts_1(A_360,A_359)
      | k1_xboole_0 = A_360
      | ~ v2_pre_topc(A_359)
      | ~ l1_pre_topc(A_359)
      | ~ r1_tarski(A_360,u1_struct_0(A_359)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2106])).

tff(c_5504,plain,(
    ! [A_360] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_360))
      | ~ v2_compts_1(A_360,k1_pre_topc('#skF_1','#skF_2'))
      | k1_xboole_0 = A_360
      | ~ v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_360,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_5489])).

tff(c_5515,plain,(
    ! [A_360] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_360))
      | ~ v2_compts_1(A_360,k1_pre_topc('#skF_1','#skF_2'))
      | k1_xboole_0 = A_360
      | ~ r1_tarski(A_360,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_205,c_5504])).

tff(c_5645,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5637,c_5515])).

tff(c_5678,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5645])).

tff(c_5679,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4294,c_5678])).

tff(c_5714,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5679])).

tff(c_32,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5075,plain,(
    ! [D_342,C_343,A_344] :
      ( v4_pre_topc(D_342,C_343)
      | ~ m1_subset_1(D_342,k1_zfmisc_1(u1_struct_0(C_343)))
      | ~ v4_pre_topc(D_342,A_344)
      | ~ m1_pre_topc(C_343,A_344)
      | ~ m1_subset_1(D_342,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5526,plain,(
    ! [A_361,C_362,A_363] :
      ( v4_pre_topc(A_361,C_362)
      | ~ v4_pre_topc(A_361,A_363)
      | ~ m1_pre_topc(C_362,A_363)
      | ~ m1_subset_1(A_361,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ l1_pre_topc(A_363)
      | ~ r1_tarski(A_361,u1_struct_0(C_362)) ) ),
    inference(resolution,[status(thm)],[c_4,c_5075])).

tff(c_5532,plain,(
    ! [A_361] :
      ( v4_pre_topc(A_361,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_361,'#skF_1')
      | ~ m1_subset_1(A_361,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_361,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_173,c_5526])).

tff(c_5557,plain,(
    ! [A_366] :
      ( v4_pre_topc(A_366,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_366,'#skF_1')
      | ~ m1_subset_1(A_366,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_366,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42,c_5532])).

tff(c_5564,plain,
    ( v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_5557])).

tff(c_5571,plain,(
    v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_5564])).

tff(c_36,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2122,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2106])).

tff(c_2133,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_36,c_2122])).

tff(c_2134,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2133])).

tff(c_20,plain,(
    ! [B_46,A_44] :
      ( v2_compts_1(B_46,A_44)
      | ~ v1_compts_1(k1_pre_topc(A_44,B_46))
      | k1_xboole_0 = B_46
      | ~ v2_pre_topc(A_44)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3108,plain,(
    ! [B_240,A_241] :
      ( v2_compts_1(B_240,A_241)
      | ~ v1_compts_1(k1_pre_topc(A_241,B_240))
      | B_240 = '#skF_2'
      | ~ v2_pre_topc(A_241)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2134,c_20])).

tff(c_3121,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_3108])).

tff(c_3132,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_3121])).

tff(c_3133,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3132])).

tff(c_3138,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3133])).

tff(c_3263,plain,(
    ! [D_247,C_248,A_249] :
      ( v4_pre_topc(D_247,C_248)
      | ~ m1_subset_1(D_247,k1_zfmisc_1(u1_struct_0(C_248)))
      | ~ v4_pre_topc(D_247,A_249)
      | ~ m1_pre_topc(C_248,A_249)
      | ~ m1_subset_1(D_247,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3755,plain,(
    ! [A_278,C_279,A_280] :
      ( v4_pre_topc(A_278,C_279)
      | ~ v4_pre_topc(A_278,A_280)
      | ~ m1_pre_topc(C_279,A_280)
      | ~ m1_subset_1(A_278,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280)
      | ~ r1_tarski(A_278,u1_struct_0(C_279)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3263])).

tff(c_3765,plain,(
    ! [A_278] :
      ( v4_pre_topc(A_278,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_278,'#skF_1')
      | ~ m1_subset_1(A_278,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_278,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_173,c_3755])).

tff(c_3786,plain,(
    ! [A_281] :
      ( v4_pre_topc(A_281,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_281,'#skF_1')
      | ~ m1_subset_1(A_281,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_281,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42,c_3765])).

tff(c_3793,plain,
    ( v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_3786])).

tff(c_3800,plain,(
    v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3793])).

tff(c_46,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_186,plain,(
    ! [A_72] :
      ( v1_compts_1(k1_pre_topc(A_72,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_72)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_196,plain,(
    ! [A_72] :
      ( v1_compts_1(k1_pre_topc(A_72,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_72)
      | ~ l1_pre_topc(A_72)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_72)) ) ),
    inference(resolution,[status(thm)],[c_4,c_186])).

tff(c_3175,plain,(
    ! [A_243] :
      ( v1_compts_1(k1_pre_topc(A_243,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_243)
      | ~ l1_pre_topc(A_243)
      | ~ r1_tarski('#skF_2',u1_struct_0(A_243)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2134,c_2134,c_2134,c_196])).

tff(c_3187,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3175])).

tff(c_3194,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_3187])).

tff(c_305,plain,(
    ! [B_87,A_88] :
      ( v2_compts_1(B_87,A_88)
      | ~ v4_pre_topc(B_87,A_88)
      | ~ v1_compts_1(A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_334,plain,(
    ! [A_89,A_90] :
      ( v2_compts_1(A_89,A_90)
      | ~ v4_pre_topc(A_89,A_90)
      | ~ v1_compts_1(A_90)
      | ~ l1_pre_topc(A_90)
      | ~ r1_tarski(A_89,u1_struct_0(A_90)) ) ),
    inference(resolution,[status(thm)],[c_4,c_305])).

tff(c_337,plain,(
    ! [A_89] :
      ( v2_compts_1(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_89,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_334])).

tff(c_348,plain,(
    ! [A_89] :
      ( v2_compts_1(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_89,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_337])).

tff(c_3682,plain,(
    ! [A_89] :
      ( v2_compts_1(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_89,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3194,c_348])).

tff(c_3806,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3800,c_3682])).

tff(c_3809,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3806])).

tff(c_3387,plain,(
    ! [A_253,C_254,D_255] :
      ( k1_pre_topc(k1_pre_topc(A_253,C_254),D_255) = k1_pre_topc(A_253,D_255)
      | ~ r1_tarski(D_255,C_254)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_253,C_254))))
      | ~ m1_subset_1(C_254,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ m1_subset_1(D_255,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4029,plain,(
    ! [A_292,C_293,A_294] :
      ( k1_pre_topc(k1_pre_topc(A_292,C_293),A_294) = k1_pre_topc(A_292,A_294)
      | ~ r1_tarski(A_294,C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ m1_subset_1(A_294,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292)
      | ~ v2_pre_topc(A_292)
      | ~ r1_tarski(A_294,u1_struct_0(k1_pre_topc(A_292,C_293))) ) ),
    inference(resolution,[status(thm)],[c_4,c_3387])).

tff(c_4044,plain,(
    ! [A_294] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_294) = k1_pre_topc('#skF_1',A_294)
      | ~ r1_tarski(A_294,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(A_294,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_294,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4029])).

tff(c_4082,plain,(
    ! [A_297] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_297) = k1_pre_topc('#skF_1',A_297)
      | ~ m1_subset_1(A_297,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_297,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_4044])).

tff(c_4089,plain,
    ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_4082])).

tff(c_4096,plain,(
    k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4089])).

tff(c_2127,plain,(
    ! [A_188,A_1] :
      ( v1_compts_1(k1_pre_topc(A_188,A_1))
      | ~ v2_compts_1(A_1,A_188)
      | k1_xboole_0 = A_1
      | ~ v2_pre_topc(A_188)
      | ~ l1_pre_topc(A_188)
      | ~ r1_tarski(A_1,u1_struct_0(A_188)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2106])).

tff(c_3560,plain,(
    ! [A_258,A_259] :
      ( v1_compts_1(k1_pre_topc(A_258,A_259))
      | ~ v2_compts_1(A_259,A_258)
      | A_259 = '#skF_2'
      | ~ v2_pre_topc(A_258)
      | ~ l1_pre_topc(A_258)
      | ~ r1_tarski(A_259,u1_struct_0(A_258)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2134,c_2127])).

tff(c_3575,plain,(
    ! [A_259] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_259))
      | ~ v2_compts_1(A_259,k1_pre_topc('#skF_1','#skF_2'))
      | A_259 = '#skF_2'
      | ~ v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_259,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_3560])).

tff(c_3586,plain,(
    ! [A_259] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_259))
      | ~ v2_compts_1(A_259,k1_pre_topc('#skF_1','#skF_2'))
      | A_259 = '#skF_2'
      | ~ r1_tarski(A_259,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_205,c_3575])).

tff(c_4121,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4096,c_3586])).

tff(c_4158,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3809,c_4121])).

tff(c_4159,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3138,c_4158])).

tff(c_4206,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4159,c_3194])).

tff(c_4231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3138,c_4206])).

tff(c_4232,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3133])).

tff(c_4253,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4232,c_36])).

tff(c_4262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4253])).

tff(c_4263,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2133])).

tff(c_5766,plain,(
    ! [A_378] :
      ( v2_compts_1(A_378,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_378,k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_378,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4263,c_348])).

tff(c_5772,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_5571,c_5766])).

tff(c_5776,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5772])).

tff(c_5778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5714,c_5776])).

tff(c_5779,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5679])).

tff(c_4478,plain,(
    ! [A_308,C_309,D_310] :
      ( k1_pre_topc(k1_pre_topc(A_308,C_309),D_310) = k1_pre_topc(A_308,D_310)
      | ~ r1_tarski(D_310,C_309)
      | ~ m1_subset_1(D_310,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_308,C_309))))
      | ~ m1_subset_1(C_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m1_subset_1(D_310,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4855,plain,(
    ! [A_333,C_334,A_335] :
      ( k1_pre_topc(k1_pre_topc(A_333,C_334),A_335) = k1_pre_topc(A_333,A_335)
      | ~ r1_tarski(A_335,C_334)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ m1_subset_1(A_335,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | ~ r1_tarski(A_335,u1_struct_0(k1_pre_topc(A_333,C_334))) ) ),
    inference(resolution,[status(thm)],[c_4,c_4478])).

tff(c_4870,plain,(
    ! [A_335] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_335) = k1_pre_topc('#skF_1',A_335)
      | ~ r1_tarski(A_335,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(A_335,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_335,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4855])).

tff(c_4887,plain,(
    ! [A_337] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_337) = k1_pre_topc('#skF_1',A_337)
      | ~ m1_subset_1(A_337,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_337,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_4870])).

tff(c_4894,plain,
    ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_4887])).

tff(c_4901,plain,(
    k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4894])).

tff(c_4588,plain,(
    ! [A_312,A_313] :
      ( v1_compts_1(k1_pre_topc(A_312,A_313))
      | ~ v2_compts_1(A_313,A_312)
      | k1_xboole_0 = A_313
      | ~ v2_pre_topc(A_312)
      | ~ l1_pre_topc(A_312)
      | ~ r1_tarski(A_313,u1_struct_0(A_312)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2106])).

tff(c_4600,plain,(
    ! [A_313] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_313))
      | ~ v2_compts_1(A_313,k1_pre_topc('#skF_1','#skF_2'))
      | k1_xboole_0 = A_313
      | ~ v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_313,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4588])).

tff(c_4611,plain,(
    ! [A_313] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_313))
      | ~ v2_compts_1(A_313,k1_pre_topc('#skF_1','#skF_2'))
      | k1_xboole_0 = A_313
      | ~ r1_tarski(A_313,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_205,c_4600])).

tff(c_4921,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4901,c_4611])).

tff(c_4955,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4921])).

tff(c_4956,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4294,c_4955])).

tff(c_4989,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4956])).

tff(c_4350,plain,(
    ! [D_301,C_302,A_303] :
      ( v4_pre_topc(D_301,C_302)
      | ~ m1_subset_1(D_301,k1_zfmisc_1(u1_struct_0(C_302)))
      | ~ v4_pre_topc(D_301,A_303)
      | ~ m1_pre_topc(C_302,A_303)
      | ~ m1_subset_1(D_301,k1_zfmisc_1(u1_struct_0(A_303)))
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4768,plain,(
    ! [A_323,C_324,A_325] :
      ( v4_pre_topc(A_323,C_324)
      | ~ v4_pre_topc(A_323,A_325)
      | ~ m1_pre_topc(C_324,A_325)
      | ~ m1_subset_1(A_323,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_pre_topc(A_325)
      | ~ r1_tarski(A_323,u1_struct_0(C_324)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4350])).

tff(c_4776,plain,(
    ! [A_323] :
      ( v4_pre_topc(A_323,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_323,'#skF_1')
      | ~ m1_subset_1(A_323,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_323,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_173,c_4768])).

tff(c_4799,plain,(
    ! [A_327] :
      ( v4_pre_topc(A_327,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_327,'#skF_1')
      | ~ m1_subset_1(A_327,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_327,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42,c_4776])).

tff(c_4806,plain,
    ( v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_4799])).

tff(c_4813,plain,(
    v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4806])).

tff(c_5027,plain,(
    ! [A_341] :
      ( v2_compts_1(A_341,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_341,k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_341,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4263,c_348])).

tff(c_5033,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4813,c_5027])).

tff(c_5037,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5033])).

tff(c_5039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4989,c_5037])).

tff(c_5041,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4956])).

tff(c_5040,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4956])).

tff(c_1424,plain,(
    ! [B_145,A_146] :
      ( v2_compts_1(B_145,A_146)
      | ~ v1_compts_1(k1_pre_topc(A_146,B_145))
      | k1_xboole_0 = B_145
      | ~ v2_pre_topc(A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1446,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1424])).

tff(c_1457,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1446])).

tff(c_1458,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1457])).

tff(c_1467,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1458])).

tff(c_1661,plain,(
    ! [A_157,C_158,D_159] :
      ( k1_pre_topc(k1_pre_topc(A_157,C_158),D_159) = k1_pre_topc(A_157,D_159)
      | ~ r1_tarski(D_159,C_158)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_157,C_158))))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ m1_subset_1(D_159,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1853,plain,(
    ! [A_176,C_177,A_178] :
      ( k1_pre_topc(k1_pre_topc(A_176,C_177),A_178) = k1_pre_topc(A_176,A_178)
      | ~ r1_tarski(A_178,C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(A_178,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | ~ r1_tarski(A_178,u1_struct_0(k1_pre_topc(A_176,C_177))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1661])).

tff(c_1868,plain,(
    ! [A_178] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_178) = k1_pre_topc('#skF_1',A_178)
      | ~ r1_tarski(A_178,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(A_178,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_178,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1853])).

tff(c_1885,plain,(
    ! [A_180] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_180) = k1_pre_topc('#skF_1',A_180)
      | ~ m1_subset_1(A_180,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_180,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1868])).

tff(c_1892,plain,
    ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1885])).

tff(c_1899,plain,(
    k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1892])).

tff(c_452,plain,(
    ! [A_94,B_95] :
      ( v1_compts_1(k1_pre_topc(A_94,B_95))
      | ~ v2_compts_1(B_95,A_94)
      | k1_xboole_0 = B_95
      | ~ v2_pre_topc(A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1724,plain,(
    ! [A_163,A_164] :
      ( v1_compts_1(k1_pre_topc(A_163,A_164))
      | ~ v2_compts_1(A_164,A_163)
      | k1_xboole_0 = A_164
      | ~ v2_pre_topc(A_163)
      | ~ l1_pre_topc(A_163)
      | ~ r1_tarski(A_164,u1_struct_0(A_163)) ) ),
    inference(resolution,[status(thm)],[c_4,c_452])).

tff(c_1739,plain,(
    ! [A_164] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_164))
      | ~ v2_compts_1(A_164,k1_pre_topc('#skF_1','#skF_2'))
      | k1_xboole_0 = A_164
      | ~ v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_164,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1724])).

tff(c_1750,plain,(
    ! [A_164] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_164))
      | ~ v2_compts_1(A_164,k1_pre_topc('#skF_1','#skF_2'))
      | k1_xboole_0 = A_164
      | ~ r1_tarski(A_164,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_205,c_1739])).

tff(c_1916,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1899,c_1750])).

tff(c_1951,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1916])).

tff(c_1952,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1467,c_1951])).

tff(c_1987,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1952])).

tff(c_1571,plain,(
    ! [D_152,C_153,A_154] :
      ( v4_pre_topc(D_152,C_153)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(u1_struct_0(C_153)))
      | ~ v4_pre_topc(D_152,A_154)
      | ~ m1_pre_topc(C_153,A_154)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1766,plain,(
    ! [A_166,C_167,A_168] :
      ( v4_pre_topc(A_166,C_167)
      | ~ v4_pre_topc(A_166,A_168)
      | ~ m1_pre_topc(C_167,A_168)
      | ~ m1_subset_1(A_166,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ r1_tarski(A_166,u1_struct_0(C_167)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1571])).

tff(c_1774,plain,(
    ! [A_166] :
      ( v4_pre_topc(A_166,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_166,'#skF_1')
      | ~ m1_subset_1(A_166,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_166,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_173,c_1766])).

tff(c_1797,plain,(
    ! [A_170] :
      ( v4_pre_topc(A_170,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_170,'#skF_1')
      | ~ m1_subset_1(A_170,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_170,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42,c_1774])).

tff(c_1804,plain,
    ( v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1797])).

tff(c_1811,plain,(
    v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1804])).

tff(c_474,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_452])).

tff(c_485,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_36,c_474])).

tff(c_486,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_622,plain,(
    ! [B_100,A_101] :
      ( v2_compts_1(B_100,A_101)
      | ~ v1_compts_1(k1_pre_topc(A_101,B_100))
      | B_100 = '#skF_2'
      | ~ v2_pre_topc(A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_20])).

tff(c_644,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_622])).

tff(c_655,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_644])).

tff(c_656,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_655])).

tff(c_661,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_760,plain,(
    ! [D_104,C_105,A_106] :
      ( v4_pre_topc(D_104,C_105)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(C_105)))
      | ~ v4_pre_topc(D_104,A_106)
      | ~ m1_pre_topc(C_105,A_106)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1073,plain,(
    ! [A_132,C_133,A_134] :
      ( v4_pre_topc(A_132,C_133)
      | ~ v4_pre_topc(A_132,A_134)
      | ~ m1_pre_topc(C_133,A_134)
      | ~ m1_subset_1(A_132,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ r1_tarski(A_132,u1_struct_0(C_133)) ) ),
    inference(resolution,[status(thm)],[c_4,c_760])).

tff(c_1083,plain,(
    ! [A_132] :
      ( v4_pre_topc(A_132,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_132,'#skF_1')
      | ~ m1_subset_1(A_132,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_132,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_173,c_1073])).

tff(c_1104,plain,(
    ! [A_135] :
      ( v4_pre_topc(A_135,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_135,'#skF_1')
      | ~ m1_subset_1(A_135,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_135,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42,c_1083])).

tff(c_1111,plain,
    ( v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1104])).

tff(c_1118,plain,(
    v4_pre_topc('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1111])).

tff(c_539,plain,(
    ! [A_97] :
      ( v1_compts_1(k1_pre_topc(A_97,'#skF_2'))
      | ~ v2_compts_1('#skF_2',A_97)
      | ~ l1_pre_topc(A_97)
      | ~ r1_tarski('#skF_2',u1_struct_0(A_97)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_486,c_486,c_196])).

tff(c_557,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_539])).

tff(c_564,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_557])).

tff(c_1003,plain,(
    ! [A_89] :
      ( v2_compts_1(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_89,k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_89,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_348])).

tff(c_1122,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1118,c_1003])).

tff(c_1125,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1122])).

tff(c_886,plain,(
    ! [A_111,C_112,D_113] :
      ( k1_pre_topc(k1_pre_topc(A_111,C_112),D_113) = k1_pre_topc(A_111,D_113)
      | ~ r1_tarski(D_113,C_112)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_111,C_112))))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(D_113,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1151,plain,(
    ! [A_139,C_140,A_141] :
      ( k1_pre_topc(k1_pre_topc(A_139,C_140),A_141) = k1_pre_topc(A_139,A_141)
      | ~ r1_tarski(A_141,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(A_141,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | ~ r1_tarski(A_141,u1_struct_0(k1_pre_topc(A_139,C_140))) ) ),
    inference(resolution,[status(thm)],[c_4,c_886])).

tff(c_1166,plain,(
    ! [A_141] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_141) = k1_pre_topc('#skF_1',A_141)
      | ~ r1_tarski(A_141,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(A_141,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_141,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1151])).

tff(c_1183,plain,(
    ! [A_143] :
      ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_143) = k1_pre_topc('#skF_1',A_143)
      | ~ m1_subset_1(A_143,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_143,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1166])).

tff(c_1190,plain,
    ( k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1183])).

tff(c_1197,plain,(
    k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1190])).

tff(c_479,plain,(
    ! [A_94,A_1] :
      ( v1_compts_1(k1_pre_topc(A_94,A_1))
      | ~ v2_compts_1(A_1,A_94)
      | k1_xboole_0 = A_1
      | ~ v2_pre_topc(A_94)
      | ~ l1_pre_topc(A_94)
      | ~ r1_tarski(A_1,u1_struct_0(A_94)) ) ),
    inference(resolution,[status(thm)],[c_4,c_452])).

tff(c_849,plain,(
    ! [A_109,A_110] :
      ( v1_compts_1(k1_pre_topc(A_109,A_110))
      | ~ v2_compts_1(A_110,A_109)
      | A_110 = '#skF_2'
      | ~ v2_pre_topc(A_109)
      | ~ l1_pre_topc(A_109)
      | ~ r1_tarski(A_110,u1_struct_0(A_109)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_479])).

tff(c_864,plain,(
    ! [A_110] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_110))
      | ~ v2_compts_1(A_110,k1_pre_topc('#skF_1','#skF_2'))
      | A_110 = '#skF_2'
      | ~ v2_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_110,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_849])).

tff(c_875,plain,(
    ! [A_110] :
      ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_110))
      | ~ v2_compts_1(A_110,k1_pre_topc('#skF_1','#skF_2'))
      | A_110 = '#skF_2'
      | ~ r1_tarski(A_110,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_205,c_864])).

tff(c_1223,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_875])).

tff(c_1261,plain,
    ( v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1125,c_1223])).

tff(c_1262,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_1261])).

tff(c_1307,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_564])).

tff(c_1329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_1307])).

tff(c_1330,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_1355,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_36])).

tff(c_1364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1355])).

tff(c_1365,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_2054,plain,(
    ! [A_187] :
      ( v2_compts_1(A_187,k1_pre_topc('#skF_1','#skF_2'))
      | ~ v4_pre_topc(A_187,k1_pre_topc('#skF_1','#skF_2'))
      | ~ r1_tarski(A_187,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_348])).

tff(c_2060,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1811,c_2054])).

tff(c_2064,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2060])).

tff(c_2066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1987,c_2064])).

tff(c_2067,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1952])).

tff(c_279,plain,(
    ! [A_84] :
      ( v1_compts_1(k1_pre_topc(A_84,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_84)
      | ~ l1_pre_topc(A_84)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_84)) ) ),
    inference(resolution,[status(thm)],[c_4,c_186])).

tff(c_282,plain,
    ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_279])).

tff(c_287,plain,
    ( v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,k1_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_282])).

tff(c_358,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_2080,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2067,c_358])).

tff(c_2088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2080])).

tff(c_2089,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1458])).

tff(c_2095,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_358])).

tff(c_2103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2095])).

tff(c_2104,plain,
    ( ~ v2_compts_1(k1_xboole_0,k1_pre_topc('#skF_1','#skF_2'))
    | v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_4295,plain,(
    ~ v2_compts_1(k1_xboole_0,k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2104])).

tff(c_5050,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5040,c_4295])).

tff(c_5072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5041,c_5050])).

tff(c_5073,plain,(
    v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_2104])).

tff(c_5788,plain,(
    v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5779,c_5073])).

tff(c_5799,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5637,c_5788])).

tff(c_5801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4294,c_5799])).

tff(c_5803,plain,(
    v1_compts_1(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4290])).

tff(c_53,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_5802,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4290])).

tff(c_246,plain,(
    ! [A_79] :
      ( v2_compts_1(k1_xboole_0,A_79)
      | ~ v1_compts_1(k1_pre_topc(A_79,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_260,plain,(
    ! [A_79] :
      ( v2_compts_1(k1_xboole_0,A_79)
      | ~ v1_compts_1(k1_pre_topc(A_79,k1_xboole_0))
      | ~ l1_pre_topc(A_79)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_246])).

tff(c_5853,plain,(
    ! [A_383] :
      ( v2_compts_1('#skF_3',A_383)
      | ~ v1_compts_1(k1_pre_topc(A_383,'#skF_3'))
      | ~ l1_pre_topc(A_383)
      | ~ r1_tarski('#skF_3',u1_struct_0(A_383)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5802,c_5802,c_5802,c_260])).

tff(c_5862,plain,
    ( v2_compts_1('#skF_3','#skF_1')
    | ~ v1_compts_1(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_53,c_5853])).

tff(c_5870,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5803,c_5862])).

tff(c_5872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_5870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.32/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.32/2.30  
% 6.32/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.30  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.49/2.30  
% 6.49/2.30  %Foreground sorts:
% 6.49/2.30  
% 6.49/2.30  
% 6.49/2.30  %Background operators:
% 6.49/2.30  
% 6.49/2.30  
% 6.49/2.30  %Foreground operators:
% 6.49/2.30  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 6.49/2.30  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 6.49/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.49/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.49/2.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.49/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.49/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.49/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.49/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.49/2.30  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.49/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.49/2.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.49/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.49/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.49/2.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.49/2.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.49/2.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.49/2.30  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 6.49/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.49/2.30  
% 6.49/2.34  tff(f_145, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 6.49/2.34  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 6.49/2.34  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 6.49/2.34  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.49/2.34  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))) => (((B = D) & r1_tarski(B, C)) => (k1_pre_topc(A, B) = k1_pre_topc(k1_pre_topc(A, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_pre_topc)).
% 6.49/2.34  tff(f_46, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 6.49/2.34  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.49/2.34  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.49/2.34  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 6.49/2.34  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_compts_1(A) & v4_pre_topc(B, A)) => v2_compts_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_compts_1)).
% 6.49/2.34  tff(c_30, plain, (~v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_4265, plain, (![B_298, A_299]: (v2_compts_1(B_298, A_299) | ~v1_compts_1(k1_pre_topc(A_299, B_298)) | k1_xboole_0=B_298 | ~v2_pre_topc(A_299) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.49/2.34  tff(c_4278, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_4265])).
% 6.49/2.34  tff(c_4289, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_4278])).
% 6.49/2.34  tff(c_4290, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_4289])).
% 6.49/2.34  tff(c_4294, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4290])).
% 6.49/2.34  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_79, plain, (![A_64, B_65]: (u1_struct_0(k1_pre_topc(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.49/2.34  tff(c_89, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_79])).
% 6.49/2.34  tff(c_96, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_89])).
% 6.49/2.34  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.49/2.34  tff(c_5137, plain, (![A_348, C_349, D_350]: (k1_pre_topc(k1_pre_topc(A_348, C_349), D_350)=k1_pre_topc(A_348, D_350) | ~r1_tarski(D_350, C_349) | ~m1_subset_1(D_350, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_348, C_349)))) | ~m1_subset_1(C_349, k1_zfmisc_1(u1_struct_0(A_348))) | ~m1_subset_1(D_350, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.34  tff(c_5592, plain, (![A_370, C_371, A_372]: (k1_pre_topc(k1_pre_topc(A_370, C_371), A_372)=k1_pre_topc(A_370, A_372) | ~r1_tarski(A_372, C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(u1_struct_0(A_370))) | ~m1_subset_1(A_372, k1_zfmisc_1(u1_struct_0(A_370))) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370) | ~r1_tarski(A_372, u1_struct_0(k1_pre_topc(A_370, C_371))))), inference(resolution, [status(thm)], [c_4, c_5137])).
% 6.49/2.34  tff(c_5607, plain, (![A_372]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_372)=k1_pre_topc('#skF_1', A_372) | ~r1_tarski(A_372, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(A_372, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_372, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_5592])).
% 6.49/2.34  tff(c_5623, plain, (![A_373]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_373)=k1_pre_topc('#skF_1', A_373) | ~m1_subset_1(A_373, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_373, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_5607])).
% 6.49/2.34  tff(c_5630, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_5623])).
% 6.49/2.34  tff(c_5637, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5630])).
% 6.49/2.34  tff(c_155, plain, (![A_70, B_71]: (m1_pre_topc(k1_pre_topc(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.49/2.34  tff(c_166, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_155])).
% 6.49/2.34  tff(c_173, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_166])).
% 6.49/2.34  tff(c_12, plain, (![B_10, A_8]: (l1_pre_topc(B_10) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.49/2.34  tff(c_202, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_173, c_12])).
% 6.49/2.34  tff(c_208, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_202])).
% 6.49/2.34  tff(c_6, plain, (![B_5, A_3]: (v2_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.49/2.34  tff(c_199, plain, (v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_173, c_6])).
% 6.49/2.34  tff(c_205, plain, (v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_199])).
% 6.49/2.34  tff(c_2106, plain, (![A_188, B_189]: (v1_compts_1(k1_pre_topc(A_188, B_189)) | ~v2_compts_1(B_189, A_188) | k1_xboole_0=B_189 | ~v2_pre_topc(A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.49/2.34  tff(c_5489, plain, (![A_359, A_360]: (v1_compts_1(k1_pre_topc(A_359, A_360)) | ~v2_compts_1(A_360, A_359) | k1_xboole_0=A_360 | ~v2_pre_topc(A_359) | ~l1_pre_topc(A_359) | ~r1_tarski(A_360, u1_struct_0(A_359)))), inference(resolution, [status(thm)], [c_4, c_2106])).
% 6.49/2.34  tff(c_5504, plain, (![A_360]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_360)) | ~v2_compts_1(A_360, k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0=A_360 | ~v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_360, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_5489])).
% 6.49/2.34  tff(c_5515, plain, (![A_360]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_360)) | ~v2_compts_1(A_360, k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0=A_360 | ~r1_tarski(A_360, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_205, c_5504])).
% 6.49/2.34  tff(c_5645, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5637, c_5515])).
% 6.49/2.34  tff(c_5678, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5645])).
% 6.49/2.34  tff(c_5679, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4294, c_5678])).
% 6.49/2.34  tff(c_5714, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5679])).
% 6.49/2.34  tff(c_32, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_5075, plain, (![D_342, C_343, A_344]: (v4_pre_topc(D_342, C_343) | ~m1_subset_1(D_342, k1_zfmisc_1(u1_struct_0(C_343))) | ~v4_pre_topc(D_342, A_344) | ~m1_pre_topc(C_343, A_344) | ~m1_subset_1(D_342, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.34  tff(c_5526, plain, (![A_361, C_362, A_363]: (v4_pre_topc(A_361, C_362) | ~v4_pre_topc(A_361, A_363) | ~m1_pre_topc(C_362, A_363) | ~m1_subset_1(A_361, k1_zfmisc_1(u1_struct_0(A_363))) | ~l1_pre_topc(A_363) | ~r1_tarski(A_361, u1_struct_0(C_362)))), inference(resolution, [status(thm)], [c_4, c_5075])).
% 6.49/2.34  tff(c_5532, plain, (![A_361]: (v4_pre_topc(A_361, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_361, '#skF_1') | ~m1_subset_1(A_361, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_361, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_173, c_5526])).
% 6.49/2.34  tff(c_5557, plain, (![A_366]: (v4_pre_topc(A_366, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_366, '#skF_1') | ~m1_subset_1(A_366, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_366, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42, c_5532])).
% 6.49/2.34  tff(c_5564, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_5557])).
% 6.49/2.34  tff(c_5571, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_5564])).
% 6.49/2.34  tff(c_36, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.49/2.34  tff(c_2122, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_compts_1('#skF_2', '#skF_1') | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2106])).
% 6.49/2.34  tff(c_2133, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_36, c_2122])).
% 6.49/2.34  tff(c_2134, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2133])).
% 6.49/2.34  tff(c_20, plain, (![B_46, A_44]: (v2_compts_1(B_46, A_44) | ~v1_compts_1(k1_pre_topc(A_44, B_46)) | k1_xboole_0=B_46 | ~v2_pre_topc(A_44) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.49/2.34  tff(c_3108, plain, (![B_240, A_241]: (v2_compts_1(B_240, A_241) | ~v1_compts_1(k1_pre_topc(A_241, B_240)) | B_240='#skF_2' | ~v2_pre_topc(A_241) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(demodulation, [status(thm), theory('equality')], [c_2134, c_20])).
% 6.49/2.34  tff(c_3121, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_3108])).
% 6.49/2.34  tff(c_3132, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_3121])).
% 6.49/2.34  tff(c_3133, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_3132])).
% 6.49/2.34  tff(c_3138, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3133])).
% 6.49/2.34  tff(c_3263, plain, (![D_247, C_248, A_249]: (v4_pre_topc(D_247, C_248) | ~m1_subset_1(D_247, k1_zfmisc_1(u1_struct_0(C_248))) | ~v4_pre_topc(D_247, A_249) | ~m1_pre_topc(C_248, A_249) | ~m1_subset_1(D_247, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.34  tff(c_3755, plain, (![A_278, C_279, A_280]: (v4_pre_topc(A_278, C_279) | ~v4_pre_topc(A_278, A_280) | ~m1_pre_topc(C_279, A_280) | ~m1_subset_1(A_278, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280) | ~r1_tarski(A_278, u1_struct_0(C_279)))), inference(resolution, [status(thm)], [c_4, c_3263])).
% 6.49/2.34  tff(c_3765, plain, (![A_278]: (v4_pre_topc(A_278, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_278, '#skF_1') | ~m1_subset_1(A_278, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_278, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_173, c_3755])).
% 6.49/2.34  tff(c_3786, plain, (![A_281]: (v4_pre_topc(A_281, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_281, '#skF_1') | ~m1_subset_1(A_281, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_281, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42, c_3765])).
% 6.49/2.34  tff(c_3793, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_3786])).
% 6.49/2.34  tff(c_3800, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3793])).
% 6.49/2.34  tff(c_46, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.49/2.34  tff(c_54, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_46])).
% 6.49/2.34  tff(c_186, plain, (![A_72]: (v1_compts_1(k1_pre_topc(A_72, k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, A_72) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.49/2.34  tff(c_196, plain, (![A_72]: (v1_compts_1(k1_pre_topc(A_72, k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, A_72) | ~l1_pre_topc(A_72) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_72)))), inference(resolution, [status(thm)], [c_4, c_186])).
% 6.49/2.34  tff(c_3175, plain, (![A_243]: (v1_compts_1(k1_pre_topc(A_243, '#skF_2')) | ~v2_compts_1('#skF_2', A_243) | ~l1_pre_topc(A_243) | ~r1_tarski('#skF_2', u1_struct_0(A_243)))), inference(demodulation, [status(thm), theory('equality')], [c_2134, c_2134, c_2134, c_196])).
% 6.49/2.34  tff(c_3187, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_compts_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_3175])).
% 6.49/2.34  tff(c_3194, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_3187])).
% 6.49/2.34  tff(c_305, plain, (![B_87, A_88]: (v2_compts_1(B_87, A_88) | ~v4_pre_topc(B_87, A_88) | ~v1_compts_1(A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.49/2.34  tff(c_334, plain, (![A_89, A_90]: (v2_compts_1(A_89, A_90) | ~v4_pre_topc(A_89, A_90) | ~v1_compts_1(A_90) | ~l1_pre_topc(A_90) | ~r1_tarski(A_89, u1_struct_0(A_90)))), inference(resolution, [status(thm)], [c_4, c_305])).
% 6.49/2.34  tff(c_337, plain, (![A_89]: (v2_compts_1(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_89, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_334])).
% 6.49/2.34  tff(c_348, plain, (![A_89]: (v2_compts_1(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_89, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_337])).
% 6.49/2.34  tff(c_3682, plain, (![A_89]: (v2_compts_1(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_89, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3194, c_348])).
% 6.49/2.34  tff(c_3806, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3800, c_3682])).
% 6.49/2.34  tff(c_3809, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3806])).
% 6.49/2.34  tff(c_3387, plain, (![A_253, C_254, D_255]: (k1_pre_topc(k1_pre_topc(A_253, C_254), D_255)=k1_pre_topc(A_253, D_255) | ~r1_tarski(D_255, C_254) | ~m1_subset_1(D_255, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_253, C_254)))) | ~m1_subset_1(C_254, k1_zfmisc_1(u1_struct_0(A_253))) | ~m1_subset_1(D_255, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.34  tff(c_4029, plain, (![A_292, C_293, A_294]: (k1_pre_topc(k1_pre_topc(A_292, C_293), A_294)=k1_pre_topc(A_292, A_294) | ~r1_tarski(A_294, C_293) | ~m1_subset_1(C_293, k1_zfmisc_1(u1_struct_0(A_292))) | ~m1_subset_1(A_294, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292) | ~v2_pre_topc(A_292) | ~r1_tarski(A_294, u1_struct_0(k1_pre_topc(A_292, C_293))))), inference(resolution, [status(thm)], [c_4, c_3387])).
% 6.49/2.34  tff(c_4044, plain, (![A_294]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_294)=k1_pre_topc('#skF_1', A_294) | ~r1_tarski(A_294, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(A_294, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_294, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4029])).
% 6.49/2.34  tff(c_4082, plain, (![A_297]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_297)=k1_pre_topc('#skF_1', A_297) | ~m1_subset_1(A_297, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_297, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_4044])).
% 6.49/2.34  tff(c_4089, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_4082])).
% 6.49/2.34  tff(c_4096, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4089])).
% 6.49/2.34  tff(c_2127, plain, (![A_188, A_1]: (v1_compts_1(k1_pre_topc(A_188, A_1)) | ~v2_compts_1(A_1, A_188) | k1_xboole_0=A_1 | ~v2_pre_topc(A_188) | ~l1_pre_topc(A_188) | ~r1_tarski(A_1, u1_struct_0(A_188)))), inference(resolution, [status(thm)], [c_4, c_2106])).
% 6.49/2.34  tff(c_3560, plain, (![A_258, A_259]: (v1_compts_1(k1_pre_topc(A_258, A_259)) | ~v2_compts_1(A_259, A_258) | A_259='#skF_2' | ~v2_pre_topc(A_258) | ~l1_pre_topc(A_258) | ~r1_tarski(A_259, u1_struct_0(A_258)))), inference(demodulation, [status(thm), theory('equality')], [c_2134, c_2127])).
% 6.49/2.34  tff(c_3575, plain, (![A_259]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_259)) | ~v2_compts_1(A_259, k1_pre_topc('#skF_1', '#skF_2')) | A_259='#skF_2' | ~v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_259, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_3560])).
% 6.49/2.34  tff(c_3586, plain, (![A_259]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_259)) | ~v2_compts_1(A_259, k1_pre_topc('#skF_1', '#skF_2')) | A_259='#skF_2' | ~r1_tarski(A_259, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_205, c_3575])).
% 6.49/2.34  tff(c_4121, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | '#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4096, c_3586])).
% 6.49/2.34  tff(c_4158, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3809, c_4121])).
% 6.49/2.34  tff(c_4159, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3138, c_4158])).
% 6.49/2.34  tff(c_4206, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4159, c_3194])).
% 6.49/2.34  tff(c_4231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3138, c_4206])).
% 6.49/2.34  tff(c_4232, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_3133])).
% 6.49/2.34  tff(c_4253, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4232, c_36])).
% 6.49/2.34  tff(c_4262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_4253])).
% 6.49/2.34  tff(c_4263, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2133])).
% 6.49/2.34  tff(c_5766, plain, (![A_378]: (v2_compts_1(A_378, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_378, k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_378, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4263, c_348])).
% 6.49/2.34  tff(c_5772, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_5571, c_5766])).
% 6.49/2.34  tff(c_5776, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5772])).
% 6.49/2.34  tff(c_5778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5714, c_5776])).
% 6.49/2.34  tff(c_5779, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5679])).
% 6.49/2.34  tff(c_4478, plain, (![A_308, C_309, D_310]: (k1_pre_topc(k1_pre_topc(A_308, C_309), D_310)=k1_pre_topc(A_308, D_310) | ~r1_tarski(D_310, C_309) | ~m1_subset_1(D_310, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_308, C_309)))) | ~m1_subset_1(C_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~m1_subset_1(D_310, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.34  tff(c_4855, plain, (![A_333, C_334, A_335]: (k1_pre_topc(k1_pre_topc(A_333, C_334), A_335)=k1_pre_topc(A_333, A_335) | ~r1_tarski(A_335, C_334) | ~m1_subset_1(C_334, k1_zfmisc_1(u1_struct_0(A_333))) | ~m1_subset_1(A_335, k1_zfmisc_1(u1_struct_0(A_333))) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | ~r1_tarski(A_335, u1_struct_0(k1_pre_topc(A_333, C_334))))), inference(resolution, [status(thm)], [c_4, c_4478])).
% 6.49/2.34  tff(c_4870, plain, (![A_335]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_335)=k1_pre_topc('#skF_1', A_335) | ~r1_tarski(A_335, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(A_335, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_335, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4855])).
% 6.49/2.34  tff(c_4887, plain, (![A_337]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_337)=k1_pre_topc('#skF_1', A_337) | ~m1_subset_1(A_337, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_337, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_4870])).
% 6.49/2.34  tff(c_4894, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_4887])).
% 6.49/2.34  tff(c_4901, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4894])).
% 6.49/2.34  tff(c_4588, plain, (![A_312, A_313]: (v1_compts_1(k1_pre_topc(A_312, A_313)) | ~v2_compts_1(A_313, A_312) | k1_xboole_0=A_313 | ~v2_pre_topc(A_312) | ~l1_pre_topc(A_312) | ~r1_tarski(A_313, u1_struct_0(A_312)))), inference(resolution, [status(thm)], [c_4, c_2106])).
% 6.49/2.34  tff(c_4600, plain, (![A_313]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_313)) | ~v2_compts_1(A_313, k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0=A_313 | ~v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_313, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4588])).
% 6.49/2.34  tff(c_4611, plain, (![A_313]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_313)) | ~v2_compts_1(A_313, k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0=A_313 | ~r1_tarski(A_313, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_205, c_4600])).
% 6.49/2.34  tff(c_4921, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4901, c_4611])).
% 6.49/2.34  tff(c_4955, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4921])).
% 6.49/2.34  tff(c_4956, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4294, c_4955])).
% 6.49/2.34  tff(c_4989, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_4956])).
% 6.49/2.34  tff(c_4350, plain, (![D_301, C_302, A_303]: (v4_pre_topc(D_301, C_302) | ~m1_subset_1(D_301, k1_zfmisc_1(u1_struct_0(C_302))) | ~v4_pre_topc(D_301, A_303) | ~m1_pre_topc(C_302, A_303) | ~m1_subset_1(D_301, k1_zfmisc_1(u1_struct_0(A_303))) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.34  tff(c_4768, plain, (![A_323, C_324, A_325]: (v4_pre_topc(A_323, C_324) | ~v4_pre_topc(A_323, A_325) | ~m1_pre_topc(C_324, A_325) | ~m1_subset_1(A_323, k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_pre_topc(A_325) | ~r1_tarski(A_323, u1_struct_0(C_324)))), inference(resolution, [status(thm)], [c_4, c_4350])).
% 6.49/2.34  tff(c_4776, plain, (![A_323]: (v4_pre_topc(A_323, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_323, '#skF_1') | ~m1_subset_1(A_323, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_323, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_173, c_4768])).
% 6.49/2.34  tff(c_4799, plain, (![A_327]: (v4_pre_topc(A_327, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_327, '#skF_1') | ~m1_subset_1(A_327, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_327, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42, c_4776])).
% 6.49/2.34  tff(c_4806, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_4799])).
% 6.49/2.34  tff(c_4813, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4806])).
% 6.49/2.34  tff(c_5027, plain, (![A_341]: (v2_compts_1(A_341, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_341, k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_341, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4263, c_348])).
% 6.49/2.34  tff(c_5033, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4813, c_5027])).
% 6.49/2.34  tff(c_5037, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5033])).
% 6.49/2.34  tff(c_5039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4989, c_5037])).
% 6.49/2.34  tff(c_5041, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_4956])).
% 6.49/2.34  tff(c_5040, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4956])).
% 6.49/2.34  tff(c_1424, plain, (![B_145, A_146]: (v2_compts_1(B_145, A_146) | ~v1_compts_1(k1_pre_topc(A_146, B_145)) | k1_xboole_0=B_145 | ~v2_pre_topc(A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.49/2.34  tff(c_1446, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1424])).
% 6.49/2.34  tff(c_1457, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1446])).
% 6.49/2.34  tff(c_1458, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_1457])).
% 6.49/2.34  tff(c_1467, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1458])).
% 6.49/2.34  tff(c_1661, plain, (![A_157, C_158, D_159]: (k1_pre_topc(k1_pre_topc(A_157, C_158), D_159)=k1_pre_topc(A_157, D_159) | ~r1_tarski(D_159, C_158) | ~m1_subset_1(D_159, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_157, C_158)))) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~m1_subset_1(D_159, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.34  tff(c_1853, plain, (![A_176, C_177, A_178]: (k1_pre_topc(k1_pre_topc(A_176, C_177), A_178)=k1_pre_topc(A_176, A_178) | ~r1_tarski(A_178, C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(A_178, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | ~r1_tarski(A_178, u1_struct_0(k1_pre_topc(A_176, C_177))))), inference(resolution, [status(thm)], [c_4, c_1661])).
% 6.49/2.34  tff(c_1868, plain, (![A_178]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_178)=k1_pre_topc('#skF_1', A_178) | ~r1_tarski(A_178, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(A_178, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_178, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1853])).
% 6.49/2.34  tff(c_1885, plain, (![A_180]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_180)=k1_pre_topc('#skF_1', A_180) | ~m1_subset_1(A_180, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_180, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1868])).
% 6.49/2.34  tff(c_1892, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1885])).
% 6.49/2.34  tff(c_1899, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1892])).
% 6.49/2.34  tff(c_452, plain, (![A_94, B_95]: (v1_compts_1(k1_pre_topc(A_94, B_95)) | ~v2_compts_1(B_95, A_94) | k1_xboole_0=B_95 | ~v2_pre_topc(A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.49/2.34  tff(c_1724, plain, (![A_163, A_164]: (v1_compts_1(k1_pre_topc(A_163, A_164)) | ~v2_compts_1(A_164, A_163) | k1_xboole_0=A_164 | ~v2_pre_topc(A_163) | ~l1_pre_topc(A_163) | ~r1_tarski(A_164, u1_struct_0(A_163)))), inference(resolution, [status(thm)], [c_4, c_452])).
% 6.49/2.34  tff(c_1739, plain, (![A_164]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_164)) | ~v2_compts_1(A_164, k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0=A_164 | ~v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_164, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1724])).
% 6.49/2.34  tff(c_1750, plain, (![A_164]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_164)) | ~v2_compts_1(A_164, k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0=A_164 | ~r1_tarski(A_164, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_205, c_1739])).
% 6.49/2.34  tff(c_1916, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1899, c_1750])).
% 6.49/2.34  tff(c_1951, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1916])).
% 6.49/2.34  tff(c_1952, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1467, c_1951])).
% 6.49/2.34  tff(c_1987, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1952])).
% 6.49/2.34  tff(c_1571, plain, (![D_152, C_153, A_154]: (v4_pre_topc(D_152, C_153) | ~m1_subset_1(D_152, k1_zfmisc_1(u1_struct_0(C_153))) | ~v4_pre_topc(D_152, A_154) | ~m1_pre_topc(C_153, A_154) | ~m1_subset_1(D_152, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.34  tff(c_1766, plain, (![A_166, C_167, A_168]: (v4_pre_topc(A_166, C_167) | ~v4_pre_topc(A_166, A_168) | ~m1_pre_topc(C_167, A_168) | ~m1_subset_1(A_166, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | ~r1_tarski(A_166, u1_struct_0(C_167)))), inference(resolution, [status(thm)], [c_4, c_1571])).
% 6.49/2.34  tff(c_1774, plain, (![A_166]: (v4_pre_topc(A_166, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_166, '#skF_1') | ~m1_subset_1(A_166, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_166, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_173, c_1766])).
% 6.49/2.34  tff(c_1797, plain, (![A_170]: (v4_pre_topc(A_170, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_170, '#skF_1') | ~m1_subset_1(A_170, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_170, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42, c_1774])).
% 6.49/2.34  tff(c_1804, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1797])).
% 6.49/2.34  tff(c_1811, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1804])).
% 6.49/2.34  tff(c_474, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_compts_1('#skF_2', '#skF_1') | k1_xboole_0='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_452])).
% 6.49/2.34  tff(c_485, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_36, c_474])).
% 6.49/2.34  tff(c_486, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_485])).
% 6.49/2.34  tff(c_622, plain, (![B_100, A_101]: (v2_compts_1(B_100, A_101) | ~v1_compts_1(k1_pre_topc(A_101, B_100)) | B_100='#skF_2' | ~v2_pre_topc(A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_20])).
% 6.49/2.34  tff(c_644, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_622])).
% 6.49/2.34  tff(c_655, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_644])).
% 6.49/2.34  tff(c_656, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_655])).
% 6.49/2.34  tff(c_661, plain, (~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_656])).
% 6.49/2.34  tff(c_760, plain, (![D_104, C_105, A_106]: (v4_pre_topc(D_104, C_105) | ~m1_subset_1(D_104, k1_zfmisc_1(u1_struct_0(C_105))) | ~v4_pre_topc(D_104, A_106) | ~m1_pre_topc(C_105, A_106) | ~m1_subset_1(D_104, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.34  tff(c_1073, plain, (![A_132, C_133, A_134]: (v4_pre_topc(A_132, C_133) | ~v4_pre_topc(A_132, A_134) | ~m1_pre_topc(C_133, A_134) | ~m1_subset_1(A_132, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~r1_tarski(A_132, u1_struct_0(C_133)))), inference(resolution, [status(thm)], [c_4, c_760])).
% 6.49/2.34  tff(c_1083, plain, (![A_132]: (v4_pre_topc(A_132, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_132, '#skF_1') | ~m1_subset_1(A_132, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_132, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_173, c_1073])).
% 6.49/2.34  tff(c_1104, plain, (![A_135]: (v4_pre_topc(A_135, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_135, '#skF_1') | ~m1_subset_1(A_135, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_135, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42, c_1083])).
% 6.49/2.34  tff(c_1111, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1104])).
% 6.49/2.34  tff(c_1118, plain, (v4_pre_topc('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1111])).
% 6.49/2.34  tff(c_539, plain, (![A_97]: (v1_compts_1(k1_pre_topc(A_97, '#skF_2')) | ~v2_compts_1('#skF_2', A_97) | ~l1_pre_topc(A_97) | ~r1_tarski('#skF_2', u1_struct_0(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_486, c_486, c_196])).
% 6.49/2.34  tff(c_557, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_compts_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_539])).
% 6.49/2.34  tff(c_564, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_557])).
% 6.49/2.34  tff(c_1003, plain, (![A_89]: (v2_compts_1(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_89, k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_89, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_564, c_348])).
% 6.49/2.34  tff(c_1122, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1118, c_1003])).
% 6.49/2.34  tff(c_1125, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1122])).
% 6.49/2.34  tff(c_886, plain, (![A_111, C_112, D_113]: (k1_pre_topc(k1_pre_topc(A_111, C_112), D_113)=k1_pre_topc(A_111, D_113) | ~r1_tarski(D_113, C_112) | ~m1_subset_1(D_113, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_111, C_112)))) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_subset_1(D_113, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.34  tff(c_1151, plain, (![A_139, C_140, A_141]: (k1_pre_topc(k1_pre_topc(A_139, C_140), A_141)=k1_pre_topc(A_139, A_141) | ~r1_tarski(A_141, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(A_141, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | ~r1_tarski(A_141, u1_struct_0(k1_pre_topc(A_139, C_140))))), inference(resolution, [status(thm)], [c_4, c_886])).
% 6.49/2.34  tff(c_1166, plain, (![A_141]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_141)=k1_pre_topc('#skF_1', A_141) | ~r1_tarski(A_141, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(A_141, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_141, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1151])).
% 6.49/2.34  tff(c_1183, plain, (![A_143]: (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_143)=k1_pre_topc('#skF_1', A_143) | ~m1_subset_1(A_143, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_143, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1166])).
% 6.49/2.34  tff(c_1190, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1183])).
% 6.49/2.34  tff(c_1197, plain, (k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1190])).
% 6.49/2.34  tff(c_479, plain, (![A_94, A_1]: (v1_compts_1(k1_pre_topc(A_94, A_1)) | ~v2_compts_1(A_1, A_94) | k1_xboole_0=A_1 | ~v2_pre_topc(A_94) | ~l1_pre_topc(A_94) | ~r1_tarski(A_1, u1_struct_0(A_94)))), inference(resolution, [status(thm)], [c_4, c_452])).
% 6.49/2.34  tff(c_849, plain, (![A_109, A_110]: (v1_compts_1(k1_pre_topc(A_109, A_110)) | ~v2_compts_1(A_110, A_109) | A_110='#skF_2' | ~v2_pre_topc(A_109) | ~l1_pre_topc(A_109) | ~r1_tarski(A_110, u1_struct_0(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_479])).
% 6.49/2.34  tff(c_864, plain, (![A_110]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_110)) | ~v2_compts_1(A_110, k1_pre_topc('#skF_1', '#skF_2')) | A_110='#skF_2' | ~v2_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_110, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_849])).
% 6.49/2.34  tff(c_875, plain, (![A_110]: (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_110)) | ~v2_compts_1(A_110, k1_pre_topc('#skF_1', '#skF_2')) | A_110='#skF_2' | ~r1_tarski(A_110, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_205, c_864])).
% 6.49/2.34  tff(c_1223, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | '#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1197, c_875])).
% 6.49/2.34  tff(c_1261, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1125, c_1223])).
% 6.49/2.34  tff(c_1262, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_661, c_1261])).
% 6.49/2.34  tff(c_1307, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_564])).
% 6.49/2.34  tff(c_1329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_661, c_1307])).
% 6.49/2.34  tff(c_1330, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_656])).
% 6.49/2.34  tff(c_1355, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_36])).
% 6.49/2.34  tff(c_1364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1355])).
% 6.49/2.34  tff(c_1365, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_485])).
% 6.49/2.34  tff(c_2054, plain, (![A_187]: (v2_compts_1(A_187, k1_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(A_187, k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(A_187, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_348])).
% 6.49/2.34  tff(c_2060, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1811, c_2054])).
% 6.49/2.34  tff(c_2064, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2060])).
% 6.49/2.34  tff(c_2066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1987, c_2064])).
% 6.49/2.34  tff(c_2067, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1952])).
% 6.49/2.34  tff(c_279, plain, (![A_84]: (v1_compts_1(k1_pre_topc(A_84, k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, A_84) | ~l1_pre_topc(A_84) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_84)))), inference(resolution, [status(thm)], [c_4, c_186])).
% 6.49/2.34  tff(c_282, plain, (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_96, c_279])).
% 6.49/2.34  tff(c_287, plain, (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, k1_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_282])).
% 6.49/2.34  tff(c_358, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_287])).
% 6.49/2.34  tff(c_2080, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2067, c_358])).
% 6.49/2.34  tff(c_2088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2080])).
% 6.49/2.34  tff(c_2089, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1458])).
% 6.49/2.34  tff(c_2095, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_358])).
% 6.49/2.34  tff(c_2103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2095])).
% 6.49/2.34  tff(c_2104, plain, (~v2_compts_1(k1_xboole_0, k1_pre_topc('#skF_1', '#skF_2')) | v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), k1_xboole_0))), inference(splitRight, [status(thm)], [c_287])).
% 6.49/2.34  tff(c_4295, plain, (~v2_compts_1(k1_xboole_0, k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2104])).
% 6.49/2.34  tff(c_5050, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5040, c_4295])).
% 6.49/2.34  tff(c_5072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5041, c_5050])).
% 6.49/2.34  tff(c_5073, plain, (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), k1_xboole_0))), inference(splitRight, [status(thm)], [c_2104])).
% 6.49/2.34  tff(c_5788, plain, (v1_compts_1(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5779, c_5073])).
% 6.49/2.34  tff(c_5799, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5637, c_5788])).
% 6.49/2.34  tff(c_5801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4294, c_5799])).
% 6.49/2.34  tff(c_5803, plain, (v1_compts_1(k1_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_4290])).
% 6.49/2.34  tff(c_53, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_46])).
% 6.49/2.34  tff(c_5802, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4290])).
% 6.49/2.34  tff(c_246, plain, (![A_79]: (v2_compts_1(k1_xboole_0, A_79) | ~v1_compts_1(k1_pre_topc(A_79, k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.49/2.34  tff(c_260, plain, (![A_79]: (v2_compts_1(k1_xboole_0, A_79) | ~v1_compts_1(k1_pre_topc(A_79, k1_xboole_0)) | ~l1_pre_topc(A_79) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_79)))), inference(resolution, [status(thm)], [c_4, c_246])).
% 6.49/2.34  tff(c_5853, plain, (![A_383]: (v2_compts_1('#skF_3', A_383) | ~v1_compts_1(k1_pre_topc(A_383, '#skF_3')) | ~l1_pre_topc(A_383) | ~r1_tarski('#skF_3', u1_struct_0(A_383)))), inference(demodulation, [status(thm), theory('equality')], [c_5802, c_5802, c_5802, c_260])).
% 6.49/2.34  tff(c_5862, plain, (v2_compts_1('#skF_3', '#skF_1') | ~v1_compts_1(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_53, c_5853])).
% 6.49/2.34  tff(c_5870, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5803, c_5862])).
% 6.49/2.34  tff(c_5872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_5870])).
% 6.49/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.49/2.34  
% 6.49/2.34  Inference rules
% 6.49/2.34  ----------------------
% 6.49/2.34  #Ref     : 0
% 6.49/2.34  #Sup     : 1209
% 6.49/2.34  #Fact    : 0
% 6.49/2.34  #Define  : 0
% 6.49/2.34  #Split   : 58
% 6.49/2.34  #Chain   : 0
% 6.49/2.34  #Close   : 0
% 6.49/2.34  
% 6.49/2.34  Ordering : KBO
% 6.49/2.34  
% 6.49/2.34  Simplification rules
% 6.49/2.34  ----------------------
% 6.49/2.34  #Subsume      : 183
% 6.49/2.34  #Demod        : 1831
% 6.49/2.34  #Tautology    : 268
% 6.49/2.34  #SimpNegUnit  : 64
% 6.49/2.34  #BackRed      : 359
% 6.49/2.34  
% 6.49/2.34  #Partial instantiations: 0
% 6.49/2.34  #Strategies tried      : 1
% 6.49/2.34  
% 6.49/2.34  Timing (in seconds)
% 6.49/2.34  ----------------------
% 6.68/2.34  Preprocessing        : 0.30
% 6.68/2.34  Parsing              : 0.16
% 6.68/2.34  CNF conversion       : 0.02
% 6.68/2.34  Main loop            : 1.20
% 6.68/2.34  Inferencing          : 0.38
% 6.68/2.34  Reduction            : 0.44
% 6.68/2.34  Demodulation         : 0.31
% 6.68/2.34  BG Simplification    : 0.05
% 6.68/2.34  Subsumption          : 0.24
% 6.68/2.34  Abstraction          : 0.05
% 6.68/2.34  MUC search           : 0.00
% 6.68/2.34  Cooper               : 0.00
% 6.68/2.34  Total                : 1.58
% 6.68/2.34  Index Insertion      : 0.00
% 6.68/2.34  Index Deletion       : 0.00
% 6.68/2.34  Index Matching       : 0.00
% 6.68/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
