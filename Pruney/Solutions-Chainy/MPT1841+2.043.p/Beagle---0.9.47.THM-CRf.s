%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:33 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 640 expanded)
%              Number of leaves         :   37 ( 233 expanded)
%              Depth                    :   16
%              Number of atoms          :  163 (1612 expanded)
%              Number of equality atoms :   53 ( 388 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_116,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_84,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_50] :
      ( v1_xboole_0(A_50)
      | r2_hidden('#skF_1'(A_50),A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_129,plain,(
    ! [A_55] :
      ( ~ r1_tarski(A_55,'#skF_1'(A_55))
      | v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_93,c_54])).

tff(c_138,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_64,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,(
    ! [A_33] :
      ( m1_subset_1('#skF_5'(A_33),A_33)
      | ~ v1_zfmisc_1(A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_240,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_465,plain,(
    ! [A_107] :
      ( k6_domain_1(A_107,'#skF_5'(A_107)) = k1_tarski('#skF_5'(A_107))
      | ~ v1_zfmisc_1(A_107)
      | v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_62,c_240])).

tff(c_60,plain,(
    ! [A_33] :
      ( k6_domain_1(A_33,'#skF_5'(A_33)) = A_33
      | ~ v1_zfmisc_1(A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_671,plain,(
    ! [A_127] :
      ( k1_tarski('#skF_5'(A_127)) = A_127
      | ~ v1_zfmisc_1(A_127)
      | v1_xboole_0(A_127)
      | ~ v1_zfmisc_1(A_127)
      | v1_xboole_0(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_60])).

tff(c_16,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [B_41,A_42] :
      ( ~ r2_hidden(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [C_16] : ~ v1_xboole_0(k1_tarski(C_16)) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    ! [A_12] :
      ( '#skF_1'(k1_tarski(A_12)) = A_12
      | v1_xboole_0(k1_tarski(A_12)) ) ),
    inference(resolution,[status(thm)],[c_93,c_14])).

tff(c_106,plain,(
    ! [A_12] : '#skF_1'(k1_tarski(A_12)) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_97])).

tff(c_755,plain,(
    ! [A_129] :
      ( '#skF_5'(A_129) = '#skF_1'(A_129)
      | ~ v1_zfmisc_1(A_129)
      | v1_xboole_0(A_129)
      | ~ v1_zfmisc_1(A_129)
      | v1_xboole_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_106])).

tff(c_757,plain,
    ( '#skF_5'('#skF_6') = '#skF_1'('#skF_6')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_755])).

tff(c_760,plain,
    ( '#skF_5'('#skF_6') = '#skF_1'('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_757])).

tff(c_761,plain,(
    '#skF_5'('#skF_6') = '#skF_1'('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_760])).

tff(c_471,plain,(
    ! [A_107] :
      ( k1_tarski('#skF_5'(A_107)) = A_107
      | ~ v1_zfmisc_1(A_107)
      | v1_xboole_0(A_107)
      | ~ v1_zfmisc_1(A_107)
      | v1_xboole_0(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_60])).

tff(c_804,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_471])).

tff(c_817,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_804])).

tff(c_818,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_817])).

tff(c_46,plain,(
    ! [A_23] : m1_subset_1('#skF_4'(A_23),k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_123,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_127,plain,(
    ! [A_23] : r1_tarski('#skF_4'(A_23),A_23) ),
    inference(resolution,[status(thm)],[c_46,c_123])).

tff(c_139,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = B_57
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [A_23] : k2_xboole_0('#skF_4'(A_23),A_23) = A_23 ),
    inference(resolution,[status(thm)],[c_127,c_139])).

tff(c_271,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_tarski(A_82) = B_81
      | k2_xboole_0(B_81,C_83) != k1_tarski(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_274,plain,(
    ! [A_23,A_82] :
      ( '#skF_4'(A_23) = k1_xboole_0
      | k1_tarski(A_82) = '#skF_4'(A_23)
      | k1_tarski(A_82) != A_23 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_271])).

tff(c_288,plain,(
    ! [A_86] :
      ( '#skF_4'(k1_tarski(A_86)) = k1_xboole_0
      | '#skF_4'(k1_tarski(A_86)) = k1_tarski(A_86) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_274])).

tff(c_300,plain,(
    ! [A_86] :
      ( r1_tarski(k1_tarski(A_86),k1_tarski(A_86))
      | '#skF_4'(k1_tarski(A_86)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_127])).

tff(c_858,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_6')),'#skF_6')
    | '#skF_4'(k1_tarski('#skF_1'('#skF_6'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_300])).

tff(c_906,plain,
    ( r1_tarski('#skF_6','#skF_6')
    | '#skF_4'('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_818,c_858])).

tff(c_1204,plain,(
    '#skF_4'('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_906])).

tff(c_44,plain,(
    ! [A_23] : ~ v1_subset_1('#skF_4'(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_412,plain,(
    ! [B_101,A_102] :
      ( ~ v1_xboole_0(B_101)
      | v1_subset_1(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102))
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_428,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0('#skF_4'(A_23))
      | v1_subset_1('#skF_4'(A_23),A_23)
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_46,c_412])).

tff(c_439,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0('#skF_4'(A_23))
      | v1_xboole_0(A_23) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_428])).

tff(c_1214,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_439])).

tff(c_1234,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1214])).

tff(c_1236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1234])).

tff(c_1238,plain,(
    '#skF_4'('#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_906])).

tff(c_68,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_195,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(A_67,B_68)
      | v1_xboole_0(B_68)
      | ~ m1_subset_1(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_199,plain,(
    ! [A_67,A_12] :
      ( A_67 = A_12
      | v1_xboole_0(k1_tarski(A_12))
      | ~ m1_subset_1(A_67,k1_tarski(A_12)) ) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_208,plain,(
    ! [A_67,A_12] :
      ( A_67 = A_12
      | ~ m1_subset_1(A_67,k1_tarski(A_12)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_199])).

tff(c_955,plain,(
    ! [A_134] :
      ( A_134 = '#skF_1'('#skF_6')
      | ~ m1_subset_1(A_134,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_208])).

tff(c_972,plain,(
    '#skF_1'('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_68,c_955])).

tff(c_978,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_818])).

tff(c_252,plain,
    ( k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_240])).

tff(c_258,plain,(
    k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_252])).

tff(c_66,plain,(
    v1_subset_1(k6_domain_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_259,plain,(
    v1_subset_1(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_66])).

tff(c_993,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_259])).

tff(c_306,plain,(
    ! [A_86] :
      ( ~ v1_subset_1(k1_tarski(A_86),k1_tarski(A_86))
      | '#skF_4'(k1_tarski(A_86)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_44])).

tff(c_861,plain,
    ( ~ v1_subset_1('#skF_6',k1_tarski('#skF_1'('#skF_6')))
    | '#skF_4'(k1_tarski('#skF_1'('#skF_6'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_306])).

tff(c_907,plain,
    ( ~ v1_subset_1('#skF_6','#skF_6')
    | '#skF_4'('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_818,c_861])).

tff(c_1267,plain,(
    '#skF_4'('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_907])).

tff(c_1268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1238,c_1267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:12:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.46  
% 3.25/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.46  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2
% 3.25/1.46  
% 3.25/1.46  %Foreground sorts:
% 3.25/1.46  
% 3.25/1.46  
% 3.25/1.46  %Background operators:
% 3.25/1.46  
% 3.25/1.46  
% 3.25/1.46  %Foreground operators:
% 3.25/1.46  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.25/1.46  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.25/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.46  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.25/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.25/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.25/1.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.25/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.25/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.25/1.46  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.25/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.46  
% 3.25/1.48  tff(f_128, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.25/1.48  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.25/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.25/1.48  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.25/1.48  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.25/1.48  tff(f_106, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.25/1.48  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.25/1.48  tff(f_84, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.25/1.48  tff(f_94, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.25/1.48  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.25/1.48  tff(f_66, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.25/1.48  tff(f_78, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 3.25/1.48  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.25/1.48  tff(c_70, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.48  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.48  tff(c_93, plain, (![A_50]: (v1_xboole_0(A_50) | r2_hidden('#skF_1'(A_50), A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.48  tff(c_54, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.25/1.48  tff(c_129, plain, (![A_55]: (~r1_tarski(A_55, '#skF_1'(A_55)) | v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_93, c_54])).
% 3.25/1.48  tff(c_138, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_129])).
% 3.25/1.48  tff(c_64, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.48  tff(c_62, plain, (![A_33]: (m1_subset_1('#skF_5'(A_33), A_33) | ~v1_zfmisc_1(A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.25/1.48  tff(c_240, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.48  tff(c_465, plain, (![A_107]: (k6_domain_1(A_107, '#skF_5'(A_107))=k1_tarski('#skF_5'(A_107)) | ~v1_zfmisc_1(A_107) | v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_62, c_240])).
% 3.25/1.48  tff(c_60, plain, (![A_33]: (k6_domain_1(A_33, '#skF_5'(A_33))=A_33 | ~v1_zfmisc_1(A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.25/1.48  tff(c_671, plain, (![A_127]: (k1_tarski('#skF_5'(A_127))=A_127 | ~v1_zfmisc_1(A_127) | v1_xboole_0(A_127) | ~v1_zfmisc_1(A_127) | v1_xboole_0(A_127))), inference(superposition, [status(thm), theory('equality')], [c_465, c_60])).
% 3.25/1.48  tff(c_16, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.48  tff(c_74, plain, (![B_41, A_42]: (~r2_hidden(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.48  tff(c_78, plain, (![C_16]: (~v1_xboole_0(k1_tarski(C_16)))), inference(resolution, [status(thm)], [c_16, c_74])).
% 3.25/1.48  tff(c_14, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.48  tff(c_97, plain, (![A_12]: ('#skF_1'(k1_tarski(A_12))=A_12 | v1_xboole_0(k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_93, c_14])).
% 3.25/1.48  tff(c_106, plain, (![A_12]: ('#skF_1'(k1_tarski(A_12))=A_12)), inference(negUnitSimplification, [status(thm)], [c_78, c_97])).
% 3.25/1.48  tff(c_755, plain, (![A_129]: ('#skF_5'(A_129)='#skF_1'(A_129) | ~v1_zfmisc_1(A_129) | v1_xboole_0(A_129) | ~v1_zfmisc_1(A_129) | v1_xboole_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_671, c_106])).
% 3.25/1.48  tff(c_757, plain, ('#skF_5'('#skF_6')='#skF_1'('#skF_6') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_64, c_755])).
% 3.25/1.48  tff(c_760, plain, ('#skF_5'('#skF_6')='#skF_1'('#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_757])).
% 3.25/1.48  tff(c_761, plain, ('#skF_5'('#skF_6')='#skF_1'('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_760])).
% 3.25/1.48  tff(c_471, plain, (![A_107]: (k1_tarski('#skF_5'(A_107))=A_107 | ~v1_zfmisc_1(A_107) | v1_xboole_0(A_107) | ~v1_zfmisc_1(A_107) | v1_xboole_0(A_107))), inference(superposition, [status(thm), theory('equality')], [c_465, c_60])).
% 3.25/1.48  tff(c_804, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_761, c_471])).
% 3.25/1.48  tff(c_817, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_804])).
% 3.25/1.48  tff(c_818, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_70, c_817])).
% 3.25/1.48  tff(c_46, plain, (![A_23]: (m1_subset_1('#skF_4'(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.48  tff(c_123, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.25/1.48  tff(c_127, plain, (![A_23]: (r1_tarski('#skF_4'(A_23), A_23))), inference(resolution, [status(thm)], [c_46, c_123])).
% 3.25/1.48  tff(c_139, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=B_57 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.48  tff(c_146, plain, (![A_23]: (k2_xboole_0('#skF_4'(A_23), A_23)=A_23)), inference(resolution, [status(thm)], [c_127, c_139])).
% 3.25/1.48  tff(c_271, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_tarski(A_82)=B_81 | k2_xboole_0(B_81, C_83)!=k1_tarski(A_82))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.25/1.48  tff(c_274, plain, (![A_23, A_82]: ('#skF_4'(A_23)=k1_xboole_0 | k1_tarski(A_82)='#skF_4'(A_23) | k1_tarski(A_82)!=A_23)), inference(superposition, [status(thm), theory('equality')], [c_146, c_271])).
% 3.25/1.48  tff(c_288, plain, (![A_86]: ('#skF_4'(k1_tarski(A_86))=k1_xboole_0 | '#skF_4'(k1_tarski(A_86))=k1_tarski(A_86))), inference(reflexivity, [status(thm), theory('equality')], [c_274])).
% 3.25/1.48  tff(c_300, plain, (![A_86]: (r1_tarski(k1_tarski(A_86), k1_tarski(A_86)) | '#skF_4'(k1_tarski(A_86))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_288, c_127])).
% 3.25/1.48  tff(c_858, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_6')), '#skF_6') | '#skF_4'(k1_tarski('#skF_1'('#skF_6')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_818, c_300])).
% 3.25/1.48  tff(c_906, plain, (r1_tarski('#skF_6', '#skF_6') | '#skF_4'('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_818, c_818, c_858])).
% 3.25/1.48  tff(c_1204, plain, ('#skF_4'('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_906])).
% 3.25/1.48  tff(c_44, plain, (![A_23]: (~v1_subset_1('#skF_4'(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.48  tff(c_412, plain, (![B_101, A_102]: (~v1_xboole_0(B_101) | v1_subset_1(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.25/1.48  tff(c_428, plain, (![A_23]: (~v1_xboole_0('#skF_4'(A_23)) | v1_subset_1('#skF_4'(A_23), A_23) | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_46, c_412])).
% 3.25/1.48  tff(c_439, plain, (![A_23]: (~v1_xboole_0('#skF_4'(A_23)) | v1_xboole_0(A_23))), inference(negUnitSimplification, [status(thm)], [c_44, c_428])).
% 3.25/1.48  tff(c_1214, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1204, c_439])).
% 3.25/1.48  tff(c_1234, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1214])).
% 3.25/1.48  tff(c_1236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1234])).
% 3.25/1.48  tff(c_1238, plain, ('#skF_4'('#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_906])).
% 3.25/1.48  tff(c_68, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.48  tff(c_195, plain, (![A_67, B_68]: (r2_hidden(A_67, B_68) | v1_xboole_0(B_68) | ~m1_subset_1(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.25/1.48  tff(c_199, plain, (![A_67, A_12]: (A_67=A_12 | v1_xboole_0(k1_tarski(A_12)) | ~m1_subset_1(A_67, k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_195, c_14])).
% 3.25/1.48  tff(c_208, plain, (![A_67, A_12]: (A_67=A_12 | ~m1_subset_1(A_67, k1_tarski(A_12)))), inference(negUnitSimplification, [status(thm)], [c_78, c_199])).
% 3.25/1.48  tff(c_955, plain, (![A_134]: (A_134='#skF_1'('#skF_6') | ~m1_subset_1(A_134, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_208])).
% 3.25/1.48  tff(c_972, plain, ('#skF_1'('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_68, c_955])).
% 3.25/1.48  tff(c_978, plain, (k1_tarski('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_972, c_818])).
% 3.25/1.48  tff(c_252, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_68, c_240])).
% 3.25/1.48  tff(c_258, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_70, c_252])).
% 3.25/1.48  tff(c_66, plain, (v1_subset_1(k6_domain_1('#skF_6', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.25/1.48  tff(c_259, plain, (v1_subset_1(k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_66])).
% 3.25/1.48  tff(c_993, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_978, c_259])).
% 3.25/1.48  tff(c_306, plain, (![A_86]: (~v1_subset_1(k1_tarski(A_86), k1_tarski(A_86)) | '#skF_4'(k1_tarski(A_86))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_288, c_44])).
% 3.25/1.48  tff(c_861, plain, (~v1_subset_1('#skF_6', k1_tarski('#skF_1'('#skF_6'))) | '#skF_4'(k1_tarski('#skF_1'('#skF_6')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_818, c_306])).
% 3.25/1.48  tff(c_907, plain, (~v1_subset_1('#skF_6', '#skF_6') | '#skF_4'('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_818, c_818, c_861])).
% 3.25/1.48  tff(c_1267, plain, ('#skF_4'('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_993, c_907])).
% 3.25/1.48  tff(c_1268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1238, c_1267])).
% 3.25/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.48  
% 3.25/1.48  Inference rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Ref     : 1
% 3.25/1.48  #Sup     : 271
% 3.25/1.48  #Fact    : 1
% 3.25/1.48  #Define  : 0
% 3.25/1.48  #Split   : 1
% 3.25/1.48  #Chain   : 0
% 3.25/1.48  #Close   : 0
% 3.25/1.48  
% 3.25/1.48  Ordering : KBO
% 3.25/1.48  
% 3.25/1.48  Simplification rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Subsume      : 37
% 3.25/1.48  #Demod        : 134
% 3.25/1.48  #Tautology    : 112
% 3.25/1.48  #SimpNegUnit  : 49
% 3.25/1.48  #BackRed      : 10
% 3.25/1.48  
% 3.25/1.48  #Partial instantiations: 0
% 3.25/1.48  #Strategies tried      : 1
% 3.25/1.48  
% 3.25/1.48  Timing (in seconds)
% 3.25/1.48  ----------------------
% 3.41/1.48  Preprocessing        : 0.34
% 3.41/1.48  Parsing              : 0.18
% 3.41/1.48  CNF conversion       : 0.03
% 3.41/1.48  Main loop            : 0.42
% 3.41/1.48  Inferencing          : 0.15
% 3.41/1.48  Reduction            : 0.13
% 3.41/1.48  Demodulation         : 0.08
% 3.41/1.48  BG Simplification    : 0.02
% 3.41/1.48  Subsumption          : 0.08
% 3.41/1.48  Abstraction          : 0.02
% 3.41/1.48  MUC search           : 0.00
% 3.41/1.48  Cooper               : 0.00
% 3.41/1.48  Total                : 0.80
% 3.41/1.48  Index Insertion      : 0.00
% 3.41/1.48  Index Deletion       : 0.00
% 3.41/1.48  Index Matching       : 0.00
% 3.41/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
