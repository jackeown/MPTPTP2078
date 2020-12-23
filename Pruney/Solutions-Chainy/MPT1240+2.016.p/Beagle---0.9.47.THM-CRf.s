%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:47 EST 2020

% Result     : Theorem 6.13s
% Output     : CNFRefutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 478 expanded)
%              Number of leaves         :   32 ( 171 expanded)
%              Depth                    :   21
%              Number of atoms          :  360 (1566 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3701,plain,(
    ! [A_384,B_385] :
      ( v3_pre_topc(k1_tops_1(A_384,B_385),A_384)
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3706,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3701])).

tff(c_3710,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3706])).

tff(c_3648,plain,(
    ! [A_377,B_378] :
      ( r1_tarski(k1_tops_1(A_377,B_378),B_378)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3653,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3648])).

tff(c_3657,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3653])).

tff(c_3243,plain,(
    ! [A_334,B_335] :
      ( v3_pre_topc(k1_tops_1(A_334,B_335),A_334)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3250,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3243])).

tff(c_3255,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3250])).

tff(c_3142,plain,(
    ! [A_320,B_321] :
      ( r1_tarski(k1_tops_1(A_320,B_321),B_321)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3147,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3142])).

tff(c_3151,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3147])).

tff(c_2804,plain,(
    ! [A_284,B_285] :
      ( v3_pre_topc(k1_tops_1(A_284,B_285),A_284)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2811,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2804])).

tff(c_2816,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2811])).

tff(c_2717,plain,(
    ! [A_272,B_273] :
      ( r1_tarski(k1_tops_1(A_272,B_273),B_273)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2722,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2717])).

tff(c_2726,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2722])).

tff(c_2310,plain,(
    ! [A_228,B_229] :
      ( v3_pre_topc(k1_tops_1(A_228,B_229),A_228)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2317,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2310])).

tff(c_2322,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2317])).

tff(c_2188,plain,(
    ! [A_208,B_209] :
      ( r1_tarski(k1_tops_1(A_208,B_209),B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2193,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2188])).

tff(c_2197,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2193])).

tff(c_50,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_61,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_63,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_54,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_87,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_54,B_55] :
      ( k3_subset_1(A_54,k3_subset_1(A_54,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_87,c_99])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_20),B_22),A_20)
      | ~ v3_pre_topc(B_22,A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1089,plain,(
    ! [A_139,B_140] :
      ( k2_pre_topc(A_139,B_140) = B_140
      | ~ v4_pre_topc(B_140,A_139)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1099,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_1089])).

tff(c_1107,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1099])).

tff(c_1123,plain,(
    ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_1201,plain,(
    ! [A_147,B_148] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_147),B_148),A_147)
      | ~ v3_pre_topc(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1211,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_1201])).

tff(c_1217,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1211])).

tff(c_1218,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1123,c_1217])).

tff(c_1306,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1218])).

tff(c_1309,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1306])).

tff(c_1313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1309])).

tff(c_1315,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k2_pre_topc(A_10,B_12) = B_12
      | ~ v4_pre_topc(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1349,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1315,c_14])).

tff(c_1361,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1349])).

tff(c_1771,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1361])).

tff(c_1774,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1771])).

tff(c_1778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87,c_61,c_1774])).

tff(c_1779,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1361])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k3_subset_1(u1_struct_0(A_13),k2_pre_topc(A_13,k3_subset_1(u1_struct_0(A_13),B_15))) = k1_tops_1(A_13,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1828,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_16])).

tff(c_1832,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87,c_104,c_1828])).

tff(c_28,plain,(
    ! [A_26,B_30,C_32] :
      ( r1_tarski(k1_tops_1(A_26,B_30),k1_tops_1(A_26,C_32))
      | ~ r1_tarski(B_30,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1870,plain,(
    ! [C_32] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_32))
      | ~ r1_tarski('#skF_4',C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_28])).

tff(c_1956,plain,(
    ! [C_182] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_182))
      | ~ r1_tarski('#skF_4',C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87,c_1870])).

tff(c_1976,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1956])).

tff(c_1988,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1976])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2001,plain,(
    ! [A_183] :
      ( r1_tarski(A_183,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_183,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1988,c_2])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ r1_tarski(k1_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2023,plain,(
    ! [A_186] :
      ( r2_hidden(A_186,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k1_tarski(A_186),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2001,c_4])).

tff(c_36,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1086,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2034,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2023,c_1086])).

tff(c_2040,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2034])).

tff(c_2044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2040])).

tff(c_2117,plain,(
    ! [D_196] :
      ( ~ r2_hidden('#skF_2',D_196)
      | ~ r1_tarski(D_196,'#skF_3')
      | ~ v3_pre_topc(D_196,'#skF_1')
      | ~ m1_subset_1(D_196,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2128,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_2117])).

tff(c_2139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_63,c_62,c_2128])).

tff(c_2140,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2141,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2363,plain,(
    ! [D_234] :
      ( ~ r2_hidden('#skF_2',D_234)
      | ~ r1_tarski(D_234,'#skF_3')
      | ~ v3_pre_topc(D_234,'#skF_1')
      | ~ m1_subset_1(D_234,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2141,c_52])).

tff(c_2367,plain,(
    ! [B_17] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_17))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_17),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_17),'#skF_1')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_2363])).

tff(c_2631,plain,(
    ! [B_254] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_254))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_254),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_254),'#skF_1')
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2367])).

tff(c_2645,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2631])).

tff(c_2656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2322,c_2197,c_2140,c_2645])).

tff(c_2657,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2772,plain,(
    ! [A_280,B_281] :
      ( m1_subset_1(k1_tops_1(A_280,B_281),k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_23,B_25] :
      ( r1_tarski(k1_tops_1(A_23,B_25),B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2781,plain,(
    ! [A_280,B_281] :
      ( r1_tarski(k1_tops_1(A_280,k1_tops_1(A_280,B_281)),k1_tops_1(A_280,B_281))
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(resolution,[status(thm)],[c_2772,c_26])).

tff(c_2950,plain,(
    ! [A_300,B_301] :
      ( r1_tarski(k1_tops_1(A_300,k1_tops_1(A_300,B_301)),k1_tops_1(A_300,B_301))
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_pre_topc(A_300) ) ),
    inference(resolution,[status(thm)],[c_2772,c_26])).

tff(c_2729,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_3')
      | ~ r1_tarski(A_1,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2726,c_2])).

tff(c_2958,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2950,c_2729])).

tff(c_2966,plain,(
    r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2958])).

tff(c_2971,plain,(
    ! [A_302] :
      ( r1_tarski(A_302,'#skF_3')
      | ~ r1_tarski(A_302,k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_2966,c_2])).

tff(c_2975,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3'))),'#skF_3')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2781,c_2971])).

tff(c_2982,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3'))),'#skF_3')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2975])).

tff(c_3060,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2982])).

tff(c_3063,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_3060])).

tff(c_3067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3063])).

tff(c_3069,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2982])).

tff(c_2658,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2692,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2658,c_44])).

tff(c_3082,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3069,c_2692])).

tff(c_3100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2816,c_2726,c_2657,c_3082])).

tff(c_3101,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3193,plain,(
    ! [A_326,B_327] :
      ( m1_subset_1(k1_tops_1(A_326,B_327),k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3102,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3166,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3102,c_40])).

tff(c_3197,plain,(
    ! [B_327] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_327))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_327),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_327),'#skF_1')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3193,c_3166])).

tff(c_3568,plain,(
    ! [B_361] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_361))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_361),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_361),'#skF_1')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3197])).

tff(c_3582,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3568])).

tff(c_3593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3151,c_3101,c_3582])).

tff(c_3594,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3729,plain,(
    ! [A_390,B_391] :
      ( m1_subset_1(k1_tops_1(A_390,B_391),k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ l1_pre_topc(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3745,plain,(
    ! [A_390,B_391] :
      ( r1_tarski(k1_tops_1(A_390,k1_tops_1(A_390,B_391)),k1_tops_1(A_390,B_391))
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ l1_pre_topc(A_390) ) ),
    inference(resolution,[status(thm)],[c_3729,c_26])).

tff(c_3884,plain,(
    ! [A_404,B_405] :
      ( r1_tarski(k1_tops_1(A_404,k1_tops_1(A_404,B_405)),k1_tops_1(A_404,B_405))
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_3729,c_26])).

tff(c_3660,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_3')
      | ~ r1_tarski(A_1,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3657,c_2])).

tff(c_3892,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3884,c_3660])).

tff(c_3900,plain,(
    r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3892])).

tff(c_3905,plain,(
    ! [A_406] :
      ( r1_tarski(A_406,'#skF_3')
      | ~ r1_tarski(A_406,k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_3900,c_2])).

tff(c_3909,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3'))),'#skF_3')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3745,c_3905])).

tff(c_3916,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3'))),'#skF_3')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3909])).

tff(c_4014,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3916])).

tff(c_4017,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_4014])).

tff(c_4021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_4017])).

tff(c_4023,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3916])).

tff(c_3595,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3619,plain,(
    ! [D_41] :
      ( ~ r2_hidden('#skF_2',D_41)
      | ~ r1_tarski(D_41,'#skF_3')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3595,c_48])).

tff(c_4036,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4023,c_3619])).

tff(c_4054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3710,c_3657,c_3594,c_4036])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.13/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.14  
% 6.13/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.14  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.13/2.14  
% 6.13/2.14  %Foreground sorts:
% 6.13/2.14  
% 6.13/2.14  
% 6.13/2.14  %Background operators:
% 6.13/2.14  
% 6.13/2.14  
% 6.13/2.14  %Foreground operators:
% 6.13/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.13/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.13/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.13/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.13/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.13/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.13/2.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.13/2.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.13/2.14  tff('#skF_2', type, '#skF_2': $i).
% 6.13/2.14  tff('#skF_3', type, '#skF_3': $i).
% 6.13/2.14  tff('#skF_1', type, '#skF_1': $i).
% 6.13/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.13/2.14  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.13/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.13/2.14  tff('#skF_4', type, '#skF_4': $i).
% 6.13/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.13/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.13/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.13/2.14  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.13/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.13/2.14  
% 6.13/2.17  tff(f_126, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 6.13/2.17  tff(f_79, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.13/2.17  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.13/2.17  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.13/2.17  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.13/2.17  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 6.13/2.17  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.13/2.17  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.13/2.17  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 6.13/2.17  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 6.13/2.17  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.13/2.17  tff(f_71, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.13/2.17  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_3701, plain, (![A_384, B_385]: (v3_pre_topc(k1_tops_1(A_384, B_385), A_384) | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0(A_384))) | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.13/2.17  tff(c_3706, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3701])).
% 6.13/2.17  tff(c_3710, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3706])).
% 6.13/2.17  tff(c_3648, plain, (![A_377, B_378]: (r1_tarski(k1_tops_1(A_377, B_378), B_378) | ~m1_subset_1(B_378, k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.13/2.17  tff(c_3653, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3648])).
% 6.13/2.17  tff(c_3657, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3653])).
% 6.13/2.17  tff(c_3243, plain, (![A_334, B_335]: (v3_pre_topc(k1_tops_1(A_334, B_335), A_334) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_334))) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.13/2.17  tff(c_3250, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3243])).
% 6.13/2.17  tff(c_3255, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3250])).
% 6.13/2.17  tff(c_3142, plain, (![A_320, B_321]: (r1_tarski(k1_tops_1(A_320, B_321), B_321) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.13/2.17  tff(c_3147, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3142])).
% 6.13/2.17  tff(c_3151, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3147])).
% 6.13/2.17  tff(c_2804, plain, (![A_284, B_285]: (v3_pre_topc(k1_tops_1(A_284, B_285), A_284) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.13/2.17  tff(c_2811, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2804])).
% 6.13/2.17  tff(c_2816, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2811])).
% 6.13/2.17  tff(c_2717, plain, (![A_272, B_273]: (r1_tarski(k1_tops_1(A_272, B_273), B_273) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.13/2.17  tff(c_2722, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2717])).
% 6.13/2.17  tff(c_2726, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2722])).
% 6.13/2.17  tff(c_2310, plain, (![A_228, B_229]: (v3_pre_topc(k1_tops_1(A_228, B_229), A_228) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.13/2.17  tff(c_2317, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2310])).
% 6.13/2.17  tff(c_2322, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2317])).
% 6.13/2.17  tff(c_2188, plain, (![A_208, B_209]: (r1_tarski(k1_tops_1(A_208, B_209), B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.13/2.17  tff(c_2193, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2188])).
% 6.13/2.17  tff(c_2197, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2193])).
% 6.13/2.17  tff(c_50, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_61, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 6.13/2.17  tff(c_46, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_63, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 6.13/2.17  tff(c_42, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_62, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 6.13/2.17  tff(c_54, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_87, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_54])).
% 6.13/2.17  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.13/2.17  tff(c_99, plain, (![A_54, B_55]: (k3_subset_1(A_54, k3_subset_1(A_54, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.13/2.17  tff(c_104, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_87, c_99])).
% 6.13/2.17  tff(c_24, plain, (![A_20, B_22]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_20), B_22), A_20) | ~v3_pre_topc(B_22, A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.13/2.17  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.13/2.17  tff(c_1089, plain, (![A_139, B_140]: (k2_pre_topc(A_139, B_140)=B_140 | ~v4_pre_topc(B_140, A_139) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.13/2.17  tff(c_1099, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_87, c_1089])).
% 6.13/2.17  tff(c_1107, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1099])).
% 6.13/2.17  tff(c_1123, plain, (~v4_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_1107])).
% 6.13/2.17  tff(c_1201, plain, (![A_147, B_148]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_147), B_148), A_147) | ~v3_pre_topc(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.13/2.17  tff(c_1211, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_104, c_1201])).
% 6.13/2.17  tff(c_1217, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1211])).
% 6.13/2.17  tff(c_1218, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1123, c_1217])).
% 6.13/2.17  tff(c_1306, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1218])).
% 6.13/2.17  tff(c_1309, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1306])).
% 6.13/2.17  tff(c_1313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_1309])).
% 6.13/2.17  tff(c_1315, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1218])).
% 6.13/2.17  tff(c_14, plain, (![A_10, B_12]: (k2_pre_topc(A_10, B_12)=B_12 | ~v4_pre_topc(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.13/2.17  tff(c_1349, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1315, c_14])).
% 6.13/2.17  tff(c_1361, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1349])).
% 6.13/2.17  tff(c_1771, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1361])).
% 6.13/2.17  tff(c_1774, plain, (~v3_pre_topc('#skF_4', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1771])).
% 6.13/2.17  tff(c_1778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_87, c_61, c_1774])).
% 6.13/2.17  tff(c_1779, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_1361])).
% 6.13/2.17  tff(c_16, plain, (![A_13, B_15]: (k3_subset_1(u1_struct_0(A_13), k2_pre_topc(A_13, k3_subset_1(u1_struct_0(A_13), B_15)))=k1_tops_1(A_13, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.13/2.17  tff(c_1828, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1779, c_16])).
% 6.13/2.17  tff(c_1832, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_87, c_104, c_1828])).
% 6.13/2.17  tff(c_28, plain, (![A_26, B_30, C_32]: (r1_tarski(k1_tops_1(A_26, B_30), k1_tops_1(A_26, C_32)) | ~r1_tarski(B_30, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.13/2.17  tff(c_1870, plain, (![C_32]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_32)) | ~r1_tarski('#skF_4', C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1832, c_28])).
% 6.13/2.17  tff(c_1956, plain, (![C_182]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_182)) | ~r1_tarski('#skF_4', C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_87, c_1870])).
% 6.13/2.17  tff(c_1976, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_1956])).
% 6.13/2.17  tff(c_1988, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1976])).
% 6.13/2.17  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.13/2.17  tff(c_2001, plain, (![A_183]: (r1_tarski(A_183, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_183, '#skF_4'))), inference(resolution, [status(thm)], [c_1988, c_2])).
% 6.13/2.17  tff(c_4, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~r1_tarski(k1_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.13/2.17  tff(c_2023, plain, (![A_186]: (r2_hidden(A_186, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tarski(A_186), '#skF_4'))), inference(resolution, [status(thm)], [c_2001, c_4])).
% 6.13/2.17  tff(c_36, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_1086, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 6.13/2.17  tff(c_2034, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_2023, c_1086])).
% 6.13/2.17  tff(c_2040, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_2034])).
% 6.13/2.17  tff(c_2044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_2040])).
% 6.13/2.17  tff(c_2117, plain, (![D_196]: (~r2_hidden('#skF_2', D_196) | ~r1_tarski(D_196, '#skF_3') | ~v3_pre_topc(D_196, '#skF_1') | ~m1_subset_1(D_196, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_36])).
% 6.13/2.17  tff(c_2128, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_2117])).
% 6.13/2.17  tff(c_2139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_63, c_62, c_2128])).
% 6.13/2.17  tff(c_2140, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 6.13/2.17  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.13/2.17  tff(c_2141, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 6.13/2.17  tff(c_52, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_2363, plain, (![D_234]: (~r2_hidden('#skF_2', D_234) | ~r1_tarski(D_234, '#skF_3') | ~v3_pre_topc(D_234, '#skF_1') | ~m1_subset_1(D_234, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2141, c_52])).
% 6.13/2.17  tff(c_2367, plain, (![B_17]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_17)) | ~r1_tarski(k1_tops_1('#skF_1', B_17), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_17), '#skF_1') | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_2363])).
% 6.13/2.17  tff(c_2631, plain, (![B_254]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_254)) | ~r1_tarski(k1_tops_1('#skF_1', B_254), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_254), '#skF_1') | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2367])).
% 6.13/2.17  tff(c_2645, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_2631])).
% 6.13/2.17  tff(c_2656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2322, c_2197, c_2140, c_2645])).
% 6.13/2.17  tff(c_2657, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 6.13/2.17  tff(c_2772, plain, (![A_280, B_281]: (m1_subset_1(k1_tops_1(A_280, B_281), k1_zfmisc_1(u1_struct_0(A_280))) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.13/2.17  tff(c_26, plain, (![A_23, B_25]: (r1_tarski(k1_tops_1(A_23, B_25), B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.13/2.17  tff(c_2781, plain, (![A_280, B_281]: (r1_tarski(k1_tops_1(A_280, k1_tops_1(A_280, B_281)), k1_tops_1(A_280, B_281)) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(resolution, [status(thm)], [c_2772, c_26])).
% 6.13/2.17  tff(c_2950, plain, (![A_300, B_301]: (r1_tarski(k1_tops_1(A_300, k1_tops_1(A_300, B_301)), k1_tops_1(A_300, B_301)) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | ~l1_pre_topc(A_300))), inference(resolution, [status(thm)], [c_2772, c_26])).
% 6.13/2.17  tff(c_2729, plain, (![A_1]: (r1_tarski(A_1, '#skF_3') | ~r1_tarski(A_1, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_2726, c_2])).
% 6.13/2.17  tff(c_2958, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2950, c_2729])).
% 6.13/2.17  tff(c_2966, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2958])).
% 6.13/2.17  tff(c_2971, plain, (![A_302]: (r1_tarski(A_302, '#skF_3') | ~r1_tarski(A_302, k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))))), inference(resolution, [status(thm)], [c_2966, c_2])).
% 6.13/2.17  tff(c_2975, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))), '#skF_3') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2781, c_2971])).
% 6.13/2.17  tff(c_2982, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))), '#skF_3') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2975])).
% 6.13/2.17  tff(c_3060, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2982])).
% 6.13/2.17  tff(c_3063, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_3060])).
% 6.13/2.17  tff(c_3067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3063])).
% 6.13/2.17  tff(c_3069, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2982])).
% 6.13/2.17  tff(c_2658, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 6.13/2.17  tff(c_44, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_2692, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2658, c_44])).
% 6.13/2.17  tff(c_3082, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_3069, c_2692])).
% 6.13/2.17  tff(c_3100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2816, c_2726, c_2657, c_3082])).
% 6.13/2.17  tff(c_3101, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 6.13/2.17  tff(c_3193, plain, (![A_326, B_327]: (m1_subset_1(k1_tops_1(A_326, B_327), k1_zfmisc_1(u1_struct_0(A_326))) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_326))) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.13/2.17  tff(c_3102, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 6.13/2.17  tff(c_40, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_3166, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_3102, c_40])).
% 6.13/2.17  tff(c_3197, plain, (![B_327]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_327)) | ~r1_tarski(k1_tops_1('#skF_1', B_327), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_327), '#skF_1') | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_3193, c_3166])).
% 6.13/2.17  tff(c_3568, plain, (![B_361]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_361)) | ~r1_tarski(k1_tops_1('#skF_1', B_361), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_361), '#skF_1') | ~m1_subset_1(B_361, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3197])).
% 6.13/2.17  tff(c_3582, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_3568])).
% 6.13/2.17  tff(c_3593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3151, c_3101, c_3582])).
% 6.13/2.17  tff(c_3594, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 6.13/2.17  tff(c_3729, plain, (![A_390, B_391]: (m1_subset_1(k1_tops_1(A_390, B_391), k1_zfmisc_1(u1_struct_0(A_390))) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0(A_390))) | ~l1_pre_topc(A_390))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.13/2.17  tff(c_3745, plain, (![A_390, B_391]: (r1_tarski(k1_tops_1(A_390, k1_tops_1(A_390, B_391)), k1_tops_1(A_390, B_391)) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0(A_390))) | ~l1_pre_topc(A_390))), inference(resolution, [status(thm)], [c_3729, c_26])).
% 6.13/2.17  tff(c_3884, plain, (![A_404, B_405]: (r1_tarski(k1_tops_1(A_404, k1_tops_1(A_404, B_405)), k1_tops_1(A_404, B_405)) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_3729, c_26])).
% 6.13/2.17  tff(c_3660, plain, (![A_1]: (r1_tarski(A_1, '#skF_3') | ~r1_tarski(A_1, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_3657, c_2])).
% 6.13/2.17  tff(c_3892, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3884, c_3660])).
% 6.13/2.17  tff(c_3900, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3892])).
% 6.13/2.17  tff(c_3905, plain, (![A_406]: (r1_tarski(A_406, '#skF_3') | ~r1_tarski(A_406, k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))))), inference(resolution, [status(thm)], [c_3900, c_2])).
% 6.13/2.17  tff(c_3909, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))), '#skF_3') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3745, c_3905])).
% 6.13/2.17  tff(c_3916, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))), '#skF_3') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3909])).
% 6.13/2.17  tff(c_4014, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_3916])).
% 6.13/2.17  tff(c_4017, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_4014])).
% 6.13/2.17  tff(c_4021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_4017])).
% 6.13/2.17  tff(c_4023, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_3916])).
% 6.13/2.17  tff(c_3595, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.13/2.17  tff(c_48, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.13/2.17  tff(c_3619, plain, (![D_41]: (~r2_hidden('#skF_2', D_41) | ~r1_tarski(D_41, '#skF_3') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_3595, c_48])).
% 6.13/2.17  tff(c_4036, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_4023, c_3619])).
% 6.13/2.17  tff(c_4054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3710, c_3657, c_3594, c_4036])).
% 6.13/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.17  
% 6.13/2.17  Inference rules
% 6.13/2.17  ----------------------
% 6.13/2.17  #Ref     : 0
% 6.13/2.17  #Sup     : 827
% 6.13/2.17  #Fact    : 0
% 6.13/2.17  #Define  : 0
% 6.13/2.17  #Split   : 52
% 6.13/2.17  #Chain   : 0
% 6.13/2.17  #Close   : 0
% 6.13/2.17  
% 6.13/2.17  Ordering : KBO
% 6.13/2.17  
% 6.13/2.17  Simplification rules
% 6.13/2.17  ----------------------
% 6.13/2.17  #Subsume      : 131
% 6.13/2.17  #Demod        : 598
% 6.13/2.17  #Tautology    : 193
% 6.13/2.17  #SimpNegUnit  : 34
% 6.13/2.17  #BackRed      : 22
% 6.13/2.17  
% 6.13/2.17  #Partial instantiations: 0
% 6.13/2.17  #Strategies tried      : 1
% 6.13/2.17  
% 6.13/2.17  Timing (in seconds)
% 6.13/2.17  ----------------------
% 6.13/2.17  Preprocessing        : 0.32
% 6.13/2.17  Parsing              : 0.18
% 6.13/2.17  CNF conversion       : 0.02
% 6.13/2.17  Main loop            : 1.07
% 6.13/2.17  Inferencing          : 0.39
% 6.13/2.17  Reduction            : 0.33
% 6.13/2.17  Demodulation         : 0.23
% 6.13/2.17  BG Simplification    : 0.04
% 6.13/2.18  Subsumption          : 0.22
% 6.13/2.18  Abstraction          : 0.04
% 6.13/2.18  MUC search           : 0.00
% 6.13/2.18  Cooper               : 0.00
% 6.13/2.18  Total                : 1.43
% 6.13/2.18  Index Insertion      : 0.00
% 6.13/2.18  Index Deletion       : 0.00
% 6.13/2.18  Index Matching       : 0.00
% 6.13/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
