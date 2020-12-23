%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:23 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 453 expanded)
%              Number of leaves         :   27 ( 166 expanded)
%              Depth                    :   12
%              Number of atoms          :  382 (1817 expanded)
%              Number of equality atoms :   46 (  94 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

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

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v4_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v5_tops_1(D,B) )
                      & ( v5_tops_1(C,A)
                       => ( v4_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(c_44,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1332,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_53,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_140,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,k1_tops_1(A_50,B_51)) = B_51
      | ~ v5_tops_1(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_150,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_144])).

tff(c_110,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k1_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( v4_pre_topc(k2_pre_topc(A_17,B_18),A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_177,plain,(
    ! [A_56,B_57] :
      ( v4_pre_topc(k2_pre_topc(A_56,k1_tops_1(A_56,B_57)),A_56)
      | ~ v2_pre_topc(A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_110,c_26])).

tff(c_180,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_177])).

tff(c_182,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_180])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_182])).

tff(c_185,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_187,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_302,plain,(
    ! [A_72,B_73] :
      ( k2_pre_topc(A_72,k1_tops_1(A_72,B_73)) = B_73
      | ~ v5_tops_1(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_306,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_302])).

tff(c_312,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_306])).

tff(c_272,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k1_tops_1(A_68,B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( r1_tarski(B_5,k2_pre_topc(A_3,B_5))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_332,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_tops_1(A_78,B_79),k2_pre_topc(A_78,k1_tops_1(A_78,B_79)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_272,c_8])).

tff(c_337,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_332])).

tff(c_340,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_337])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_211,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,B_61) = B_61
      | ~ v4_pre_topc(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_211])).

tff(c_220,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_186,c_214])).

tff(c_192,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,k2_pre_topc(A_59,B_58))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_194,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_192])).

tff(c_199,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_194])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_209,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_232,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_209])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_232])).

tff(c_237,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_413,plain,(
    ! [B_92,A_93] :
      ( v4_tops_1(B_92,A_93)
      | ~ r1_tarski(B_92,k2_pre_topc(A_93,k1_tops_1(A_93,B_92)))
      | ~ r1_tarski(k1_tops_1(A_93,k2_pre_topc(A_93,B_92)),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_422,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_413])).

tff(c_427,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_340,c_6,c_312,c_422])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_427])).

tff(c_430,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_431,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_433,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_431,c_42])).

tff(c_509,plain,(
    ! [A_102,B_103] :
      ( k2_pre_topc(A_102,B_103) = B_103
      | ~ v4_pre_topc(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_515,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_509])).

tff(c_521,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_430,c_515])).

tff(c_436,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(B_94,k2_pre_topc(A_95,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_440,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_436])).

tff(c_446,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_440])).

tff(c_452,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_446,c_2])).

tff(c_508,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_522,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_508])).

tff(c_526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_522])).

tff(c_527,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_620,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k1_tops_1(A_118,k2_pre_topc(A_118,B_119)),B_119)
      | ~ v4_tops_1(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_628,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_620])).

tff(c_636,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_433,c_628])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_682,plain,(
    ! [A_128,C_129,B_130] :
      ( r1_tarski(k2_pre_topc(A_128,C_129),B_130)
      | ~ r1_tarski(C_129,B_130)
      | ~ v4_pre_topc(B_130,A_128)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_751,plain,(
    ! [A_137,B_138,B_139] :
      ( r1_tarski(k2_pre_topc(A_137,k1_tops_1(A_137,B_138)),B_139)
      | ~ r1_tarski(k1_tops_1(A_137,B_138),B_139)
      | ~ v4_pre_topc(B_139,A_137)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_24,c_682])).

tff(c_643,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(B_120,k2_pre_topc(A_121,k1_tops_1(A_121,B_120)))
      | ~ v4_tops_1(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_649,plain,(
    ! [A_121,B_120] :
      ( k2_pre_topc(A_121,k1_tops_1(A_121,B_120)) = B_120
      | ~ r1_tarski(k2_pre_topc(A_121,k1_tops_1(A_121,B_120)),B_120)
      | ~ v4_tops_1(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_643,c_2])).

tff(c_913,plain,(
    ! [A_146,B_147] :
      ( k2_pre_topc(A_146,k1_tops_1(A_146,B_147)) = B_147
      | ~ v4_tops_1(B_147,A_146)
      | ~ r1_tarski(k1_tops_1(A_146,B_147),B_147)
      | ~ v4_pre_topc(B_147,A_146)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(resolution,[status(thm)],[c_751,c_649])).

tff(c_915,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_636,c_913])).

tff(c_920,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_430,c_433,c_915])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v5_tops_1(B_14,A_12)
      | k2_pre_topc(A_12,k1_tops_1(A_12,B_14)) != B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_953,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_20])).

tff(c_976,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_953])).

tff(c_978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_976])).

tff(c_979,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_980,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_981,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_980,c_48])).

tff(c_1022,plain,(
    ! [A_154,B_155] :
      ( k2_pre_topc(A_154,B_155) = B_155
      | ~ v4_pre_topc(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1028,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1022])).

tff(c_1034,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_979,c_1028])).

tff(c_991,plain,(
    ! [B_150,A_151] :
      ( r1_tarski(B_150,k2_pre_topc(A_151,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_995,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_991])).

tff(c_1001,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_995])).

tff(c_1007,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1001,c_2])).

tff(c_1009,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1007])).

tff(c_1035,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1009])).

tff(c_1039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1035])).

tff(c_1040,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1007])).

tff(c_1127,plain,(
    ! [A_174,B_175] :
      ( r1_tarski(k1_tops_1(A_174,k2_pre_topc(A_174,B_175)),B_175)
      | ~ v4_tops_1(B_175,A_174)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1132,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_1127])).

tff(c_1135,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_981,c_1132])).

tff(c_1156,plain,(
    ! [A_180,C_181,B_182] :
      ( r1_tarski(k2_pre_topc(A_180,C_181),B_182)
      | ~ r1_tarski(C_181,B_182)
      | ~ v4_pre_topc(B_182,A_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1239,plain,(
    ! [A_196,B_197,B_198] :
      ( r1_tarski(k2_pre_topc(A_196,k1_tops_1(A_196,B_197)),B_198)
      | ~ r1_tarski(k1_tops_1(A_196,B_197),B_198)
      | ~ v4_pre_topc(B_198,A_196)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_24,c_1156])).

tff(c_1122,plain,(
    ! [B_170,A_171] :
      ( r1_tarski(B_170,k2_pre_topc(A_171,k1_tops_1(A_171,B_170)))
      | ~ v4_tops_1(B_170,A_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1125,plain,(
    ! [A_171,B_170] :
      ( k2_pre_topc(A_171,k1_tops_1(A_171,B_170)) = B_170
      | ~ r1_tarski(k2_pre_topc(A_171,k1_tops_1(A_171,B_170)),B_170)
      | ~ v4_tops_1(B_170,A_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_1122,c_2])).

tff(c_1260,plain,(
    ! [A_199,B_200] :
      ( k2_pre_topc(A_199,k1_tops_1(A_199,B_200)) = B_200
      | ~ v4_tops_1(B_200,A_199)
      | ~ r1_tarski(k1_tops_1(A_199,B_200),B_200)
      | ~ v4_pre_topc(B_200,A_199)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_1239,c_1125])).

tff(c_1262,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1135,c_1260])).

tff(c_1265,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_979,c_981,c_1262])).

tff(c_1295,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_20])).

tff(c_1318,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1295])).

tff(c_1320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1318])).

tff(c_1321,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1412,plain,(
    ! [A_215,B_216] :
      ( k2_pre_topc(A_215,k1_tops_1(A_215,B_216)) = B_216
      | ~ v5_tops_1(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1416,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1412])).

tff(c_1422,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1321,c_1416])).

tff(c_1380,plain,(
    ! [A_209,B_210] :
      ( m1_subset_1(k1_tops_1(A_209,B_210),k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1444,plain,(
    ! [A_217,B_218] :
      ( v4_pre_topc(k2_pre_topc(A_217,k1_tops_1(A_217,B_218)),A_217)
      | ~ v2_pre_topc(A_217)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(resolution,[status(thm)],[c_1380,c_26])).

tff(c_1450,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_1444])).

tff(c_1455,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_1450])).

tff(c_1457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1332,c_1455])).

tff(c_1459,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1458,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1460,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1458])).

tff(c_1574,plain,(
    ! [A_233,B_234] :
      ( k2_pre_topc(A_233,k1_tops_1(A_233,B_234)) = B_234
      | ~ v5_tops_1(B_234,A_233)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1578,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1574])).

tff(c_1584,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1321,c_1578])).

tff(c_1535,plain,(
    ! [A_227,B_228] :
      ( m1_subset_1(k1_tops_1(A_227,B_228),k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1637,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(k1_tops_1(A_241,B_242),k2_pre_topc(A_241,k1_tops_1(A_241,B_242)))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_1535,c_8])).

tff(c_1645,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1584,c_1637])).

tff(c_1650,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1645])).

tff(c_1503,plain,(
    ! [A_225,B_226] :
      ( k2_pre_topc(A_225,B_226) = B_226
      | ~ v4_pre_topc(B_226,A_225)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1509,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1503])).

tff(c_1516,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1459,c_1509])).

tff(c_1465,plain,(
    ! [B_219,A_220] :
      ( r1_tarski(B_219,k2_pre_topc(A_220,B_219))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1467,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1465])).

tff(c_1472,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1467])).

tff(c_1478,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1472,c_2])).

tff(c_1482,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1478])).

tff(c_1521,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1482])).

tff(c_1526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1521])).

tff(c_1527,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1478])).

tff(c_1792,plain,(
    ! [B_262,A_263] :
      ( v4_tops_1(B_262,A_263)
      | ~ r1_tarski(B_262,k2_pre_topc(A_263,k1_tops_1(A_263,B_262)))
      | ~ r1_tarski(k1_tops_1(A_263,k2_pre_topc(A_263,B_262)),B_262)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1804,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_1792])).

tff(c_1811,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1650,c_6,c_1584,c_1804])).

tff(c_1813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1460,c_1811])).

tff(c_1815,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1458])).

tff(c_1322,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1815,c_1322,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.64  
% 3.85/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.65  %$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.65  
% 3.85/1.65  %Foreground sorts:
% 3.85/1.65  
% 3.85/1.65  
% 3.85/1.65  %Background operators:
% 3.85/1.65  
% 3.85/1.65  
% 3.85/1.65  %Foreground operators:
% 3.85/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.65  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 3.85/1.65  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.85/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.85/1.65  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.85/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.65  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.85/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.65  
% 3.85/1.67  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v4_pre_topc(D, B) & v4_tops_1(D, B)) => v5_tops_1(D, B)) & (v5_tops_1(C, A) => (v4_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tops_1)).
% 3.85/1.67  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 3.85/1.67  tff(f_79, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.85/1.67  tff(f_87, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.85/1.67  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.85/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.85/1.67  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.85/1.67  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 3.85/1.67  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 3.85/1.67  tff(c_44, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_1332, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 3.85/1.67  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_46, plain, (~v5_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_53, plain, (~v5_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 3.85/1.67  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_64, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 3.85/1.67  tff(c_50, plain, (v4_pre_topc('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_54, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 3.85/1.67  tff(c_140, plain, (![A_50, B_51]: (k2_pre_topc(A_50, k1_tops_1(A_50, B_51))=B_51 | ~v5_tops_1(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.85/1.67  tff(c_144, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_140])).
% 3.85/1.67  tff(c_150, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_144])).
% 3.85/1.67  tff(c_110, plain, (![A_46, B_47]: (m1_subset_1(k1_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.85/1.67  tff(c_26, plain, (![A_17, B_18]: (v4_pre_topc(k2_pre_topc(A_17, B_18), A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.85/1.67  tff(c_177, plain, (![A_56, B_57]: (v4_pre_topc(k2_pre_topc(A_56, k1_tops_1(A_56, B_57)), A_56) | ~v2_pre_topc(A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_110, c_26])).
% 3.85/1.67  tff(c_180, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_150, c_177])).
% 3.85/1.67  tff(c_182, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_180])).
% 3.85/1.67  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_182])).
% 3.85/1.67  tff(c_185, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.85/1.67  tff(c_187, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_185])).
% 3.85/1.67  tff(c_302, plain, (![A_72, B_73]: (k2_pre_topc(A_72, k1_tops_1(A_72, B_73))=B_73 | ~v5_tops_1(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.85/1.67  tff(c_306, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_302])).
% 3.85/1.67  tff(c_312, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_306])).
% 3.85/1.67  tff(c_272, plain, (![A_68, B_69]: (m1_subset_1(k1_tops_1(A_68, B_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.85/1.67  tff(c_8, plain, (![B_5, A_3]: (r1_tarski(B_5, k2_pre_topc(A_3, B_5)) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.67  tff(c_332, plain, (![A_78, B_79]: (r1_tarski(k1_tops_1(A_78, B_79), k2_pre_topc(A_78, k1_tops_1(A_78, B_79))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_272, c_8])).
% 3.85/1.67  tff(c_337, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_312, c_332])).
% 3.85/1.67  tff(c_340, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_337])).
% 3.85/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.67  tff(c_186, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 3.85/1.67  tff(c_211, plain, (![A_60, B_61]: (k2_pre_topc(A_60, B_61)=B_61 | ~v4_pre_topc(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_214, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_211])).
% 3.85/1.67  tff(c_220, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_186, c_214])).
% 3.85/1.67  tff(c_192, plain, (![B_58, A_59]: (r1_tarski(B_58, k2_pre_topc(A_59, B_58)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.67  tff(c_194, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_192])).
% 3.85/1.67  tff(c_199, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_194])).
% 3.85/1.67  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.67  tff(c_205, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_199, c_2])).
% 3.85/1.67  tff(c_209, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_205])).
% 3.85/1.67  tff(c_232, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_209])).
% 3.85/1.67  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_232])).
% 3.85/1.67  tff(c_237, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_205])).
% 3.85/1.67  tff(c_413, plain, (![B_92, A_93]: (v4_tops_1(B_92, A_93) | ~r1_tarski(B_92, k2_pre_topc(A_93, k1_tops_1(A_93, B_92))) | ~r1_tarski(k1_tops_1(A_93, k2_pre_topc(A_93, B_92)), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.67  tff(c_422, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_237, c_413])).
% 3.85/1.67  tff(c_427, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_340, c_6, c_312, c_422])).
% 3.85/1.67  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_427])).
% 3.85/1.67  tff(c_430, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_185])).
% 3.85/1.67  tff(c_431, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_185])).
% 3.85/1.67  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_433, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_431, c_42])).
% 3.85/1.67  tff(c_509, plain, (![A_102, B_103]: (k2_pre_topc(A_102, B_103)=B_103 | ~v4_pre_topc(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_515, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_509])).
% 3.85/1.67  tff(c_521, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_430, c_515])).
% 3.85/1.67  tff(c_436, plain, (![B_94, A_95]: (r1_tarski(B_94, k2_pre_topc(A_95, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.67  tff(c_440, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_436])).
% 3.85/1.67  tff(c_446, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_440])).
% 3.85/1.67  tff(c_452, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_446, c_2])).
% 3.85/1.67  tff(c_508, plain, (~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_452])).
% 3.85/1.67  tff(c_522, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_508])).
% 3.85/1.67  tff(c_526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_522])).
% 3.85/1.67  tff(c_527, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_452])).
% 3.85/1.67  tff(c_620, plain, (![A_118, B_119]: (r1_tarski(k1_tops_1(A_118, k2_pre_topc(A_118, B_119)), B_119) | ~v4_tops_1(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.67  tff(c_628, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_527, c_620])).
% 3.85/1.67  tff(c_636, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_433, c_628])).
% 3.85/1.67  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.85/1.67  tff(c_682, plain, (![A_128, C_129, B_130]: (r1_tarski(k2_pre_topc(A_128, C_129), B_130) | ~r1_tarski(C_129, B_130) | ~v4_pre_topc(B_130, A_128) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.85/1.67  tff(c_751, plain, (![A_137, B_138, B_139]: (r1_tarski(k2_pre_topc(A_137, k1_tops_1(A_137, B_138)), B_139) | ~r1_tarski(k1_tops_1(A_137, B_138), B_139) | ~v4_pre_topc(B_139, A_137) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_24, c_682])).
% 3.85/1.67  tff(c_643, plain, (![B_120, A_121]: (r1_tarski(B_120, k2_pre_topc(A_121, k1_tops_1(A_121, B_120))) | ~v4_tops_1(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.67  tff(c_649, plain, (![A_121, B_120]: (k2_pre_topc(A_121, k1_tops_1(A_121, B_120))=B_120 | ~r1_tarski(k2_pre_topc(A_121, k1_tops_1(A_121, B_120)), B_120) | ~v4_tops_1(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_643, c_2])).
% 3.85/1.67  tff(c_913, plain, (![A_146, B_147]: (k2_pre_topc(A_146, k1_tops_1(A_146, B_147))=B_147 | ~v4_tops_1(B_147, A_146) | ~r1_tarski(k1_tops_1(A_146, B_147), B_147) | ~v4_pre_topc(B_147, A_146) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(resolution, [status(thm)], [c_751, c_649])).
% 3.85/1.67  tff(c_915, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_636, c_913])).
% 3.85/1.67  tff(c_920, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_430, c_433, c_915])).
% 3.85/1.67  tff(c_20, plain, (![B_14, A_12]: (v5_tops_1(B_14, A_12) | k2_pre_topc(A_12, k1_tops_1(A_12, B_14))!=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.85/1.67  tff(c_953, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_920, c_20])).
% 3.85/1.67  tff(c_976, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_953])).
% 3.85/1.67  tff(c_978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_976])).
% 3.85/1.67  tff(c_979, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.85/1.67  tff(c_980, plain, (~v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 3.85/1.67  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_981, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_980, c_48])).
% 3.85/1.67  tff(c_1022, plain, (![A_154, B_155]: (k2_pre_topc(A_154, B_155)=B_155 | ~v4_pre_topc(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_1028, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1022])).
% 3.85/1.67  tff(c_1034, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_979, c_1028])).
% 3.85/1.67  tff(c_991, plain, (![B_150, A_151]: (r1_tarski(B_150, k2_pre_topc(A_151, B_150)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.67  tff(c_995, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_991])).
% 3.85/1.67  tff(c_1001, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_995])).
% 3.85/1.67  tff(c_1007, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1001, c_2])).
% 3.85/1.67  tff(c_1009, plain, (~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1007])).
% 3.85/1.67  tff(c_1035, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1009])).
% 3.85/1.67  tff(c_1039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1035])).
% 3.85/1.67  tff(c_1040, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1007])).
% 3.85/1.67  tff(c_1127, plain, (![A_174, B_175]: (r1_tarski(k1_tops_1(A_174, k2_pre_topc(A_174, B_175)), B_175) | ~v4_tops_1(B_175, A_174) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.67  tff(c_1132, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1040, c_1127])).
% 3.85/1.67  tff(c_1135, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_981, c_1132])).
% 3.85/1.67  tff(c_1156, plain, (![A_180, C_181, B_182]: (r1_tarski(k2_pre_topc(A_180, C_181), B_182) | ~r1_tarski(C_181, B_182) | ~v4_pre_topc(B_182, A_180) | ~m1_subset_1(C_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.85/1.67  tff(c_1239, plain, (![A_196, B_197, B_198]: (r1_tarski(k2_pre_topc(A_196, k1_tops_1(A_196, B_197)), B_198) | ~r1_tarski(k1_tops_1(A_196, B_197), B_198) | ~v4_pre_topc(B_198, A_196) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_196))) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(resolution, [status(thm)], [c_24, c_1156])).
% 3.85/1.67  tff(c_1122, plain, (![B_170, A_171]: (r1_tarski(B_170, k2_pre_topc(A_171, k1_tops_1(A_171, B_170))) | ~v4_tops_1(B_170, A_171) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.67  tff(c_1125, plain, (![A_171, B_170]: (k2_pre_topc(A_171, k1_tops_1(A_171, B_170))=B_170 | ~r1_tarski(k2_pre_topc(A_171, k1_tops_1(A_171, B_170)), B_170) | ~v4_tops_1(B_170, A_171) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_1122, c_2])).
% 3.85/1.67  tff(c_1260, plain, (![A_199, B_200]: (k2_pre_topc(A_199, k1_tops_1(A_199, B_200))=B_200 | ~v4_tops_1(B_200, A_199) | ~r1_tarski(k1_tops_1(A_199, B_200), B_200) | ~v4_pre_topc(B_200, A_199) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_1239, c_1125])).
% 3.85/1.67  tff(c_1262, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1135, c_1260])).
% 3.85/1.67  tff(c_1265, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_979, c_981, c_1262])).
% 3.85/1.67  tff(c_1295, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1265, c_20])).
% 3.85/1.67  tff(c_1318, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1295])).
% 3.85/1.67  tff(c_1320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1318])).
% 3.85/1.67  tff(c_1321, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.85/1.67  tff(c_1412, plain, (![A_215, B_216]: (k2_pre_topc(A_215, k1_tops_1(A_215, B_216))=B_216 | ~v5_tops_1(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.85/1.67  tff(c_1416, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1412])).
% 3.85/1.67  tff(c_1422, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1321, c_1416])).
% 3.85/1.67  tff(c_1380, plain, (![A_209, B_210]: (m1_subset_1(k1_tops_1(A_209, B_210), k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.85/1.67  tff(c_1444, plain, (![A_217, B_218]: (v4_pre_topc(k2_pre_topc(A_217, k1_tops_1(A_217, B_218)), A_217) | ~v2_pre_topc(A_217) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(resolution, [status(thm)], [c_1380, c_26])).
% 3.85/1.67  tff(c_1450, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1422, c_1444])).
% 3.85/1.67  tff(c_1455, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_1450])).
% 3.85/1.67  tff(c_1457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1332, c_1455])).
% 3.85/1.67  tff(c_1459, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 3.85/1.67  tff(c_1458, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.85/1.67  tff(c_1460, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1458])).
% 3.85/1.67  tff(c_1574, plain, (![A_233, B_234]: (k2_pre_topc(A_233, k1_tops_1(A_233, B_234))=B_234 | ~v5_tops_1(B_234, A_233) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.85/1.67  tff(c_1578, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1574])).
% 3.85/1.67  tff(c_1584, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1321, c_1578])).
% 3.85/1.67  tff(c_1535, plain, (![A_227, B_228]: (m1_subset_1(k1_tops_1(A_227, B_228), k1_zfmisc_1(u1_struct_0(A_227))) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.85/1.67  tff(c_1637, plain, (![A_241, B_242]: (r1_tarski(k1_tops_1(A_241, B_242), k2_pre_topc(A_241, k1_tops_1(A_241, B_242))) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_1535, c_8])).
% 3.85/1.67  tff(c_1645, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1584, c_1637])).
% 3.85/1.67  tff(c_1650, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1645])).
% 3.85/1.67  tff(c_1503, plain, (![A_225, B_226]: (k2_pre_topc(A_225, B_226)=B_226 | ~v4_pre_topc(B_226, A_225) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_1509, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1503])).
% 3.85/1.67  tff(c_1516, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1459, c_1509])).
% 3.85/1.67  tff(c_1465, plain, (![B_219, A_220]: (r1_tarski(B_219, k2_pre_topc(A_220, B_219)) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.67  tff(c_1467, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1465])).
% 3.85/1.67  tff(c_1472, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1467])).
% 3.85/1.67  tff(c_1478, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1472, c_2])).
% 3.85/1.67  tff(c_1482, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1478])).
% 3.85/1.67  tff(c_1521, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_1482])).
% 3.85/1.67  tff(c_1526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1521])).
% 3.85/1.67  tff(c_1527, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1478])).
% 3.85/1.67  tff(c_1792, plain, (![B_262, A_263]: (v4_tops_1(B_262, A_263) | ~r1_tarski(B_262, k2_pre_topc(A_263, k1_tops_1(A_263, B_262))) | ~r1_tarski(k1_tops_1(A_263, k2_pre_topc(A_263, B_262)), B_262) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.67  tff(c_1804, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1527, c_1792])).
% 3.85/1.67  tff(c_1811, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1650, c_6, c_1584, c_1804])).
% 3.85/1.67  tff(c_1813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1460, c_1811])).
% 3.85/1.67  tff(c_1815, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1458])).
% 3.85/1.67  tff(c_1322, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.85/1.67  tff(c_40, plain, (~v5_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.85/1.67  tff(c_1819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1815, c_1322, c_40])).
% 3.85/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.67  
% 3.85/1.67  Inference rules
% 3.85/1.67  ----------------------
% 3.85/1.67  #Ref     : 0
% 3.85/1.67  #Sup     : 332
% 3.85/1.67  #Fact    : 0
% 3.85/1.68  #Define  : 0
% 3.85/1.68  #Split   : 58
% 3.85/1.68  #Chain   : 0
% 3.85/1.68  #Close   : 0
% 3.85/1.68  
% 3.85/1.68  Ordering : KBO
% 3.85/1.68  
% 3.85/1.68  Simplification rules
% 3.85/1.68  ----------------------
% 3.85/1.68  #Subsume      : 51
% 3.85/1.68  #Demod        : 509
% 3.85/1.68  #Tautology    : 114
% 3.85/1.68  #SimpNegUnit  : 25
% 3.85/1.68  #BackRed      : 17
% 3.85/1.68  
% 3.85/1.68  #Partial instantiations: 0
% 3.85/1.68  #Strategies tried      : 1
% 3.85/1.68  
% 3.85/1.68  Timing (in seconds)
% 3.85/1.68  ----------------------
% 3.85/1.68  Preprocessing        : 0.32
% 3.85/1.68  Parsing              : 0.18
% 3.85/1.68  CNF conversion       : 0.02
% 3.85/1.68  Main loop            : 0.56
% 3.85/1.68  Inferencing          : 0.20
% 3.85/1.68  Reduction            : 0.18
% 3.85/1.68  Demodulation         : 0.13
% 3.85/1.68  BG Simplification    : 0.02
% 3.85/1.68  Subsumption          : 0.11
% 3.85/1.68  Abstraction          : 0.03
% 3.85/1.68  MUC search           : 0.00
% 3.85/1.68  Cooper               : 0.00
% 3.85/1.68  Total                : 0.94
% 3.85/1.68  Index Insertion      : 0.00
% 3.85/1.68  Index Deletion       : 0.00
% 3.85/1.68  Index Matching       : 0.00
% 3.85/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
