%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:55 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 181 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  178 ( 590 expanded)
%              Number of equality atoms :   33 (  93 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_49,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_165,plain,(
    ! [B_71,A_72] :
      ( v2_tops_1(B_71,A_72)
      | k1_tops_1(A_72,B_71) != k1_xboole_0
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_172,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_165])).

tff(c_176,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_172])).

tff(c_177,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_176])).

tff(c_77,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_86,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_82])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_154,plain,(
    ! [A_67,B_68] :
      ( v3_pre_topc(k1_tops_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_159,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_154])).

tff(c_163,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_159])).

tff(c_52,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_61,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_50,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_61])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [C_44] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_44
      | ~ v3_pre_topc(C_44,'#skF_1')
      | ~ r1_tarski(C_44,'#skF_2')
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_179,plain,(
    ! [C_73] :
      ( k1_xboole_0 = C_73
      | ~ v3_pre_topc(C_73,'#skF_1')
      | ~ r1_tarski(C_73,'#skF_2')
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_48])).

tff(c_189,plain,(
    ! [A_74] :
      ( k1_xboole_0 = A_74
      | ~ v3_pre_topc(A_74,'#skF_1')
      | ~ r1_tarski(A_74,'#skF_2')
      | ~ r1_tarski(A_74,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_203,plain,(
    ! [A_75] :
      ( k1_xboole_0 = A_75
      | ~ v3_pre_topc(A_75,'#skF_1')
      | ~ r1_tarski(A_75,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_189])).

tff(c_210,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_203])).

tff(c_219,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_210])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_219])).

tff(c_222,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_223,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_228,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_32])).

tff(c_36,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_240,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_36])).

tff(c_382,plain,(
    ! [A_97,B_98] :
      ( k1_tops_1(A_97,B_98) = k1_xboole_0
      | ~ v2_tops_1(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_385,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_240,c_382])).

tff(c_395,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_385])).

tff(c_419,plain,(
    ~ v2_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_421,plain,(
    ! [B_101,A_102] :
      ( v2_tops_1(B_101,A_102)
      | k1_tops_1(A_102,B_101) != k1_xboole_0
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_424,plain,
    ( v2_tops_1('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_240,c_421])).

tff(c_434,plain,
    ( v2_tops_1('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_424])).

tff(c_435,plain,(
    k1_tops_1('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_434])).

tff(c_34,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_226,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_34])).

tff(c_392,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_382])).

tff(c_399,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_223,c_392])).

tff(c_550,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_tarski(k1_tops_1(A_108,B_109),k1_tops_1(A_108,C_110))
      | ~ r1_tarski(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_578,plain,(
    ! [B_109] :
      ( r1_tarski(k1_tops_1('#skF_1',B_109),k1_xboole_0)
      | ~ r1_tarski(B_109,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_550])).

tff(c_919,plain,(
    ! [B_122] :
      ( r1_tarski(k1_tops_1('#skF_1',B_122),k1_xboole_0)
      | ~ r1_tarski(B_122,'#skF_2')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_578])).

tff(c_922,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_240,c_919])).

tff(c_932,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_922])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_951,plain,(
    k1_tops_1('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_932,c_4])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_951])).

tff(c_967,plain,(
    k1_tops_1('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_18,plain,(
    ! [B_27,D_33,C_31,A_19] :
      ( k1_tops_1(B_27,D_33) = D_33
      | ~ v3_pre_topc(D_33,B_27)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(u1_struct_0(B_27)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(B_27)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1334,plain,(
    ! [C_140,A_141] :
      ( ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_1337,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_240,c_1334])).

tff(c_1348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1337])).

tff(c_1549,plain,(
    ! [B_150,D_151] :
      ( k1_tops_1(B_150,D_151) = D_151
      | ~ v3_pre_topc(D_151,B_150)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ l1_pre_topc(B_150) ) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_1552,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_240,c_1549])).

tff(c_1562,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_228,c_967,c_1552])).

tff(c_1564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_1562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.54  
% 3.53/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.55  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.53/1.55  
% 3.53/1.55  %Foreground sorts:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Background operators:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Foreground operators:
% 3.53/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.55  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.53/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.53/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.53/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.53/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.55  
% 3.53/1.56  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.53/1.56  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.53/1.56  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.53/1.56  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.53/1.56  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.56  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.53/1.56  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 3.53/1.56  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.53/1.56  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.53/1.56  tff(c_30, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_49, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.53/1.56  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_165, plain, (![B_71, A_72]: (v2_tops_1(B_71, A_72) | k1_tops_1(A_72, B_71)!=k1_xboole_0 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.53/1.56  tff(c_172, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_165])).
% 3.53/1.56  tff(c_176, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_172])).
% 3.53/1.56  tff(c_177, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_49, c_176])).
% 3.53/1.56  tff(c_77, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.53/1.56  tff(c_82, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_77])).
% 3.53/1.56  tff(c_86, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_82])).
% 3.53/1.56  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_154, plain, (![A_67, B_68]: (v3_pre_topc(k1_tops_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.53/1.56  tff(c_159, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_154])).
% 3.53/1.56  tff(c_163, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_159])).
% 3.53/1.56  tff(c_52, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.56  tff(c_60, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_52])).
% 3.53/1.56  tff(c_61, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.56  tff(c_64, plain, (![A_50]: (r1_tarski(A_50, u1_struct_0('#skF_1')) | ~r1_tarski(A_50, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_61])).
% 3.53/1.56  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.56  tff(c_48, plain, (![C_44]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_44 | ~v3_pre_topc(C_44, '#skF_1') | ~r1_tarski(C_44, '#skF_2') | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_179, plain, (![C_73]: (k1_xboole_0=C_73 | ~v3_pre_topc(C_73, '#skF_1') | ~r1_tarski(C_73, '#skF_2') | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_49, c_48])).
% 3.53/1.56  tff(c_189, plain, (![A_74]: (k1_xboole_0=A_74 | ~v3_pre_topc(A_74, '#skF_1') | ~r1_tarski(A_74, '#skF_2') | ~r1_tarski(A_74, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_179])).
% 3.53/1.56  tff(c_203, plain, (![A_75]: (k1_xboole_0=A_75 | ~v3_pre_topc(A_75, '#skF_1') | ~r1_tarski(A_75, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_189])).
% 3.53/1.56  tff(c_210, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_163, c_203])).
% 3.53/1.56  tff(c_219, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_210])).
% 3.53/1.56  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_219])).
% 3.53/1.56  tff(c_222, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.53/1.56  tff(c_223, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.53/1.56  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_228, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_32])).
% 3.53/1.56  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_240, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_36])).
% 3.53/1.56  tff(c_382, plain, (![A_97, B_98]: (k1_tops_1(A_97, B_98)=k1_xboole_0 | ~v2_tops_1(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.53/1.56  tff(c_385, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_240, c_382])).
% 3.53/1.56  tff(c_395, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_385])).
% 3.53/1.56  tff(c_419, plain, (~v2_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_395])).
% 3.53/1.56  tff(c_421, plain, (![B_101, A_102]: (v2_tops_1(B_101, A_102) | k1_tops_1(A_102, B_101)!=k1_xboole_0 | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.53/1.56  tff(c_424, plain, (v2_tops_1('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_240, c_421])).
% 3.53/1.56  tff(c_434, plain, (v2_tops_1('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_424])).
% 3.53/1.56  tff(c_435, plain, (k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_419, c_434])).
% 3.53/1.56  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.53/1.56  tff(c_226, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_34])).
% 3.53/1.56  tff(c_392, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_382])).
% 3.53/1.56  tff(c_399, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_223, c_392])).
% 3.53/1.56  tff(c_550, plain, (![A_108, B_109, C_110]: (r1_tarski(k1_tops_1(A_108, B_109), k1_tops_1(A_108, C_110)) | ~r1_tarski(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.53/1.56  tff(c_578, plain, (![B_109]: (r1_tarski(k1_tops_1('#skF_1', B_109), k1_xboole_0) | ~r1_tarski(B_109, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_550])).
% 3.53/1.56  tff(c_919, plain, (![B_122]: (r1_tarski(k1_tops_1('#skF_1', B_122), k1_xboole_0) | ~r1_tarski(B_122, '#skF_2') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_578])).
% 3.53/1.56  tff(c_922, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_240, c_919])).
% 3.53/1.56  tff(c_932, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_922])).
% 3.53/1.56  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.56  tff(c_951, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_932, c_4])).
% 3.53/1.56  tff(c_966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_951])).
% 3.53/1.56  tff(c_967, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_395])).
% 3.53/1.56  tff(c_18, plain, (![B_27, D_33, C_31, A_19]: (k1_tops_1(B_27, D_33)=D_33 | ~v3_pre_topc(D_33, B_27) | ~m1_subset_1(D_33, k1_zfmisc_1(u1_struct_0(B_27))) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(B_27) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.53/1.56  tff(c_1334, plain, (![C_140, A_141]: (~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(splitLeft, [status(thm)], [c_18])).
% 3.53/1.56  tff(c_1337, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_240, c_1334])).
% 3.53/1.56  tff(c_1348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1337])).
% 3.53/1.56  tff(c_1549, plain, (![B_150, D_151]: (k1_tops_1(B_150, D_151)=D_151 | ~v3_pre_topc(D_151, B_150) | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0(B_150))) | ~l1_pre_topc(B_150))), inference(splitRight, [status(thm)], [c_18])).
% 3.53/1.56  tff(c_1552, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_240, c_1549])).
% 3.53/1.56  tff(c_1562, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_228, c_967, c_1552])).
% 3.53/1.56  tff(c_1564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_1562])).
% 3.53/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  Inference rules
% 3.53/1.56  ----------------------
% 3.53/1.56  #Ref     : 0
% 3.53/1.56  #Sup     : 339
% 3.53/1.56  #Fact    : 0
% 3.53/1.56  #Define  : 0
% 3.53/1.56  #Split   : 12
% 3.53/1.56  #Chain   : 0
% 3.53/1.56  #Close   : 0
% 3.53/1.56  
% 3.53/1.56  Ordering : KBO
% 3.53/1.56  
% 3.53/1.56  Simplification rules
% 3.53/1.56  ----------------------
% 3.53/1.56  #Subsume      : 97
% 3.53/1.56  #Demod        : 263
% 3.53/1.56  #Tautology    : 109
% 3.53/1.56  #SimpNegUnit  : 6
% 3.53/1.56  #BackRed      : 7
% 3.53/1.56  
% 3.53/1.56  #Partial instantiations: 0
% 3.53/1.56  #Strategies tried      : 1
% 3.53/1.56  
% 3.53/1.56  Timing (in seconds)
% 3.53/1.56  ----------------------
% 3.53/1.57  Preprocessing        : 0.32
% 3.53/1.57  Parsing              : 0.17
% 3.53/1.57  CNF conversion       : 0.02
% 3.53/1.57  Main loop            : 0.48
% 3.53/1.57  Inferencing          : 0.16
% 3.53/1.57  Reduction            : 0.15
% 3.53/1.57  Demodulation         : 0.10
% 3.53/1.57  BG Simplification    : 0.02
% 3.53/1.57  Subsumption          : 0.11
% 3.53/1.57  Abstraction          : 0.02
% 3.53/1.57  MUC search           : 0.00
% 3.53/1.57  Cooper               : 0.00
% 3.53/1.57  Total                : 0.83
% 3.53/1.57  Index Insertion      : 0.00
% 3.53/1.57  Index Deletion       : 0.00
% 3.53/1.57  Index Matching       : 0.00
% 3.53/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
