%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0963+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:08 EST 2020

% Result     : Theorem 13.29s
% Output     : CNFRefutation 13.60s
% Verified   : 
% Statistics : Number of formulae       :  237 (1964 expanded)
%              Number of leaves         :   42 ( 647 expanded)
%              Depth                    :   19
%              Number of atoms          :  433 (4822 expanded)
%              Number of equality atoms :   57 ( 670 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k1_relat_1(C) = A
            & ! [D] :
                ( r2_hidden(D,A)
               => r2_hidden(k1_funct_1(C,D),B) ) )
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_76,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_79,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_72,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_125,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),A_93)
      | r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_1'(A_8,B_9),B_9)
      | r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_133,plain,(
    ! [A_93] : r1_tarski(A_93,A_93) ),
    inference(resolution,[status(thm)],[c_125,c_18])).

tff(c_68,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_45137,plain,(
    ! [C_2302,A_2303,B_2304] :
      ( m1_subset_1(C_2302,k1_zfmisc_1(k2_zfmisc_1(A_2303,B_2304)))
      | ~ r1_tarski(k2_relat_1(C_2302),B_2304)
      | ~ r1_tarski(k1_relat_1(C_2302),A_2303)
      | ~ v1_relat_1(C_2302) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_96,plain,(
    ! [D_83] :
      ( r2_hidden(k1_funct_1('#skF_9',D_83),'#skF_8')
      | ~ r2_hidden(D_83,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_62,plain,(
    ! [B_76,A_75] :
      ( ~ v1_xboole_0(B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_100,plain,(
    ! [D_83] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(D_83,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_96,c_62])).

tff(c_101,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_70,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64])).

tff(c_136,plain,(
    ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_1'(A_8,B_9),A_8)
      | r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_27768,plain,(
    ! [A_1432,C_1433] :
      ( r2_hidden('#skF_5'(A_1432,k2_relat_1(A_1432),C_1433),k1_relat_1(A_1432))
      | ~ r2_hidden(C_1433,k2_relat_1(A_1432))
      | ~ v1_funct_1(A_1432)
      | ~ v1_relat_1(A_1432) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_27783,plain,(
    ! [C_1433] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1433),'#skF_7')
      | ~ r2_hidden(C_1433,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_27768])).

tff(c_27790,plain,(
    ! [C_1433] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1433),'#skF_7')
      | ~ r2_hidden(C_1433,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_27783])).

tff(c_28275,plain,(
    ! [A_1456,C_1457] :
      ( k1_funct_1(A_1456,'#skF_5'(A_1456,k2_relat_1(A_1456),C_1457)) = C_1457
      | ~ r2_hidden(C_1457,k2_relat_1(A_1456))
      | ~ v1_funct_1(A_1456)
      | ~ v1_relat_1(A_1456) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    ! [D_78] :
      ( r2_hidden(k1_funct_1('#skF_9',D_78),'#skF_8')
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_28297,plain,(
    ! [C_1457] :
      ( r2_hidden(C_1457,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1457),'#skF_7')
      | ~ r2_hidden(C_1457,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28275,c_66])).

tff(c_28412,plain,(
    ! [C_1466] :
      ( r2_hidden(C_1466,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1466),'#skF_7')
      | ~ r2_hidden(C_1466,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_28297])).

tff(c_28423,plain,(
    ! [C_1467] :
      ( r2_hidden(C_1467,'#skF_8')
      | ~ r2_hidden(C_1467,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_27790,c_28412])).

tff(c_28531,plain,(
    ! [B_1473] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_1473),'#skF_8')
      | r1_tarski(k2_relat_1('#skF_9'),B_1473) ) ),
    inference(resolution,[status(thm)],[c_20,c_28423])).

tff(c_28548,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_28531,c_18])).

tff(c_28565,plain,(
    ! [C_1474,A_1475,B_1476] :
      ( m1_subset_1(C_1474,k1_zfmisc_1(k2_zfmisc_1(A_1475,B_1476)))
      | ~ r1_tarski(k2_relat_1(C_1474),B_1476)
      | ~ r1_tarski(k1_relat_1(C_1474),A_1475)
      | ~ v1_relat_1(C_1474) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34722,plain,(
    ! [C_1673,A_1674,B_1675] :
      ( r1_tarski(C_1673,k2_zfmisc_1(A_1674,B_1675))
      | ~ r1_tarski(k2_relat_1(C_1673),B_1675)
      | ~ r1_tarski(k1_relat_1(C_1673),A_1674)
      | ~ v1_relat_1(C_1673) ) ),
    inference(resolution,[status(thm)],[c_28565,c_52])).

tff(c_34726,plain,(
    ! [A_1674] :
      ( r1_tarski('#skF_9',k2_zfmisc_1(A_1674,'#skF_8'))
      | ~ r1_tarski(k1_relat_1('#skF_9'),A_1674)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_28548,c_34722])).

tff(c_34739,plain,(
    ! [A_1676] :
      ( r1_tarski('#skF_9',k2_zfmisc_1(A_1676,'#skF_8'))
      | ~ r1_tarski('#skF_7',A_1676) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_34726])).

tff(c_54,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(A_66,k1_zfmisc_1(B_67))
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2970,plain,(
    ! [A_292,B_293,C_294] :
      ( k1_relset_1(A_292,B_293,C_294) = k1_relat_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2983,plain,(
    ! [A_292,B_293,A_66] :
      ( k1_relset_1(A_292,B_293,A_66) = k1_relat_1(A_66)
      | ~ r1_tarski(A_66,k2_zfmisc_1(A_292,B_293)) ) ),
    inference(resolution,[status(thm)],[c_54,c_2970])).

tff(c_34764,plain,(
    ! [A_1676] :
      ( k1_relset_1(A_1676,'#skF_8','#skF_9') = k1_relat_1('#skF_9')
      | ~ r1_tarski('#skF_7',A_1676) ) ),
    inference(resolution,[status(thm)],[c_34739,c_2983])).

tff(c_34795,plain,(
    ! [A_1677] :
      ( k1_relset_1(A_1677,'#skF_8','#skF_9') = '#skF_7'
      | ~ r1_tarski('#skF_7',A_1677) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34764])).

tff(c_34805,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_133,c_34795])).

tff(c_48,plain,(
    ! [C_63,A_61,B_62] :
      ( m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ r1_tarski(k2_relat_1(C_63),B_62)
      | ~ r1_tarski(k1_relat_1(C_63),A_61)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [A_53,B_54,C_55] :
      ( m1_subset_1(k1_relset_1(A_53,B_54,C_55),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34816,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34805,c_40])).

tff(c_36571,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_34816])).

tff(c_36574,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_36571])).

tff(c_36581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_133,c_68,c_28548,c_36574])).

tff(c_36583,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_34816])).

tff(c_10,plain,(
    ! [B_6,C_7,A_5] :
      ( k1_xboole_0 = B_6
      | v1_funct_2(C_7,A_5,B_6)
      | k1_relset_1(A_5,B_6,C_7) != A_5
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36740,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2('#skF_9','#skF_7','#skF_8')
    | k1_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_36583,c_10])).

tff(c_36762,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34805,c_36740])).

tff(c_36763,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_36762])).

tff(c_138,plain,(
    ! [C_98,B_99,A_100] :
      ( r2_hidden(C_98,B_99)
      | ~ r2_hidden(C_98,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_147,plain,(
    ! [D_78,B_99] :
      ( r2_hidden(k1_funct_1('#skF_9',D_78),B_99)
      | ~ r1_tarski('#skF_8',B_99)
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_138])).

tff(c_42,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    ! [A_79] :
      ( k1_xboole_0 = A_79
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_83,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_42])).

tff(c_167,plain,(
    ! [C_106,B_107,A_108] :
      ( v1_xboole_0(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(B_107,A_108)))
      | ~ v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2944,plain,(
    ! [A_289,A_290,B_291] :
      ( v1_xboole_0(A_289)
      | ~ v1_xboole_0(A_290)
      | ~ r1_tarski(A_289,k2_zfmisc_1(B_291,A_290)) ) ),
    inference(resolution,[status(thm)],[c_54,c_167])).

tff(c_2985,plain,(
    ! [B_295,A_296] :
      ( v1_xboole_0(k2_zfmisc_1(B_295,A_296))
      | ~ v1_xboole_0(A_296) ) ),
    inference(resolution,[status(thm)],[c_133,c_2944])).

tff(c_60,plain,(
    ! [A_74] :
      ( k1_xboole_0 = A_74
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2990,plain,(
    ! [B_297,A_298] :
      ( k2_zfmisc_1(B_297,A_298) = k1_xboole_0
      | ~ v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_2985,c_60])).

tff(c_3000,plain,(
    ! [B_299] : k2_zfmisc_1(B_299,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_2990])).

tff(c_44,plain,(
    ! [A_56] : m1_subset_1('#skF_6'(A_56),A_56) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_189,plain,(
    ! [B_114,A_115] :
      ( v1_xboole_0('#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_114,A_115))))
      | ~ v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_44,c_167])).

tff(c_2883,plain,(
    ! [B_280,A_281] :
      ( '#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_280,A_281))) = k1_xboole_0
      | ~ v1_xboole_0(A_281) ) ),
    inference(resolution,[status(thm)],[c_189,c_60])).

tff(c_2904,plain,(
    ! [B_280,A_281] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(B_280,A_281)))
      | ~ v1_xboole_0(A_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2883,c_44])).

tff(c_3014,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3000,c_2904])).

tff(c_3035,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3014])).

tff(c_58,plain,(
    ! [C_73,B_72,A_71] :
      ( ~ v1_xboole_0(C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3072,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3035,c_58])).

tff(c_3082,plain,(
    ! [A_302] : ~ r2_hidden(A_302,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3072])).

tff(c_3095,plain,(
    ! [D_78] :
      ( ~ r1_tarski('#skF_8',k1_xboole_0)
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_147,c_3082])).

tff(c_3200,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3095])).

tff(c_36851,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36763,c_3200])).

tff(c_36866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_36851])).

tff(c_36868,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3095])).

tff(c_176,plain,(
    ! [A_66,A_108,B_107] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0(A_108)
      | ~ r1_tarski(A_66,k2_zfmisc_1(B_107,A_108)) ) ),
    inference(resolution,[status(thm)],[c_54,c_167])).

tff(c_3011,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3000,c_176])).

tff(c_3033,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3011])).

tff(c_36975,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_36868,c_3033])).

tff(c_36984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_36975])).

tff(c_36985,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_45162,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_45137,c_36985])).

tff(c_45187,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_133,c_68,c_45162])).

tff(c_45659,plain,(
    ! [A_2320,C_2321] :
      ( r2_hidden('#skF_5'(A_2320,k2_relat_1(A_2320),C_2321),k1_relat_1(A_2320))
      | ~ r2_hidden(C_2321,k2_relat_1(A_2320))
      | ~ v1_funct_1(A_2320)
      | ~ v1_relat_1(A_2320) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_45683,plain,(
    ! [C_2321] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2321),'#skF_7')
      | ~ r2_hidden(C_2321,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_45659])).

tff(c_45720,plain,(
    ! [C_2324] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2324),'#skF_7')
      | ~ r2_hidden(C_2324,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_45683])).

tff(c_44877,plain,(
    ! [A_2284,C_2285] :
      ( k1_funct_1(A_2284,'#skF_5'(A_2284,k2_relat_1(A_2284),C_2285)) = C_2285
      | ~ r2_hidden(C_2285,k2_relat_1(A_2284))
      | ~ v1_funct_1(A_2284)
      | ~ v1_relat_1(A_2284) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44899,plain,(
    ! [C_2285] :
      ( r2_hidden(C_2285,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2285),'#skF_7')
      | ~ r2_hidden(C_2285,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44877,c_66])).

tff(c_44911,plain,(
    ! [C_2285] :
      ( r2_hidden(C_2285,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2285),'#skF_7')
      | ~ r2_hidden(C_2285,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_44899])).

tff(c_45739,plain,(
    ! [C_2325] :
      ( r2_hidden(C_2325,'#skF_8')
      | ~ r2_hidden(C_2325,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_45720,c_44911])).

tff(c_46223,plain,(
    ! [B_2346] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_2346),'#skF_8')
      | r1_tarski(k2_relat_1('#skF_9'),B_2346) ) ),
    inference(resolution,[status(thm)],[c_20,c_45739])).

tff(c_46233,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_46223,c_18])).

tff(c_46243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45187,c_45187,c_46233])).

tff(c_46245,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_48480,plain,(
    ! [A_2526,B_2527] :
      ( ~ r2_hidden('#skF_1'(A_2526,B_2527),B_2527)
      | r1_tarski(A_2526,B_2527) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48485,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_20,c_48480])).

tff(c_48603,plain,(
    ! [C_2550,B_2551,A_2552] :
      ( v1_xboole_0(C_2550)
      | ~ m1_subset_1(C_2550,k1_zfmisc_1(k2_zfmisc_1(B_2551,A_2552)))
      | ~ v1_xboole_0(A_2552) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48660,plain,(
    ! [A_2559,A_2560,B_2561] :
      ( v1_xboole_0(A_2559)
      | ~ v1_xboole_0(A_2560)
      | ~ r1_tarski(A_2559,k2_zfmisc_1(B_2561,A_2560)) ) ),
    inference(resolution,[status(thm)],[c_54,c_48603])).

tff(c_48687,plain,(
    ! [B_2562,A_2563] :
      ( v1_xboole_0(k2_zfmisc_1(B_2562,A_2563))
      | ~ v1_xboole_0(A_2563) ) ),
    inference(resolution,[status(thm)],[c_48485,c_48660])).

tff(c_46249,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46245,c_60])).

tff(c_46252,plain,(
    ! [A_74] :
      ( A_74 = '#skF_8'
      | ~ v1_xboole_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46249,c_60])).

tff(c_48703,plain,(
    ! [B_2567,A_2568] :
      ( k2_zfmisc_1(B_2567,A_2568) = '#skF_8'
      | ~ v1_xboole_0(A_2568) ) ),
    inference(resolution,[status(thm)],[c_48687,c_46252])).

tff(c_48712,plain,(
    ! [B_2567] : k2_zfmisc_1(B_2567,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46245,c_48703])).

tff(c_48487,plain,(
    ! [A_2529,B_2530] :
      ( r2_hidden(A_2529,B_2530)
      | v1_xboole_0(B_2530)
      | ~ m1_subset_1(A_2529,B_2530) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46244,plain,(
    ! [D_83] : ~ r2_hidden(D_83,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_48500,plain,(
    ! [A_2529] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_2529,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48487,c_46244])).

tff(c_48503,plain,(
    ! [A_2531] : ~ m1_subset_1(A_2531,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_48500])).

tff(c_48508,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_44,c_48503])).

tff(c_48509,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_48500])).

tff(c_48521,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_48509,c_46252])).

tff(c_46330,plain,(
    ! [A_2360,B_2361] :
      ( r2_hidden('#skF_1'(A_2360,B_2361),A_2360)
      | r1_tarski(A_2360,B_2361) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46343,plain,(
    ! [A_2360] : r1_tarski(A_2360,A_2360) ),
    inference(resolution,[status(thm)],[c_46330,c_18])).

tff(c_46382,plain,(
    ! [C_2379,B_2380,A_2381] :
      ( v1_xboole_0(C_2379)
      | ~ m1_subset_1(C_2379,k1_zfmisc_1(k2_zfmisc_1(B_2380,A_2381)))
      | ~ v1_xboole_0(A_2381) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46456,plain,(
    ! [A_2391,A_2392,B_2393] :
      ( v1_xboole_0(A_2391)
      | ~ v1_xboole_0(A_2392)
      | ~ r1_tarski(A_2391,k2_zfmisc_1(B_2393,A_2392)) ) ),
    inference(resolution,[status(thm)],[c_54,c_46382])).

tff(c_46494,plain,(
    ! [B_2397,A_2398] :
      ( v1_xboole_0(k2_zfmisc_1(B_2397,A_2398))
      | ~ v1_xboole_0(A_2398) ) ),
    inference(resolution,[status(thm)],[c_46343,c_46456])).

tff(c_46499,plain,(
    ! [B_2399,A_2400] :
      ( k2_zfmisc_1(B_2399,A_2400) = '#skF_8'
      | ~ v1_xboole_0(A_2400) ) ),
    inference(resolution,[status(thm)],[c_46494,c_46252])).

tff(c_46509,plain,(
    ! [B_2401] : k2_zfmisc_1(B_2401,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46245,c_46499])).

tff(c_46393,plain,(
    ! [B_2382,A_2383] :
      ( v1_xboole_0('#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_2382,A_2383))))
      | ~ v1_xboole_0(A_2383) ) ),
    inference(resolution,[status(thm)],[c_44,c_46382])).

tff(c_46415,plain,(
    ! [B_2387,A_2388] :
      ( '#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_2387,A_2388))) = '#skF_8'
      | ~ v1_xboole_0(A_2388) ) ),
    inference(resolution,[status(thm)],[c_46393,c_46252])).

tff(c_46433,plain,(
    ! [B_2387,A_2388] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_2387,A_2388)))
      | ~ v1_xboole_0(A_2388) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46415,c_44])).

tff(c_46520,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46509,c_46433])).

tff(c_46538,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46245,c_46520])).

tff(c_46508,plain,(
    ! [B_2399] : k2_zfmisc_1(B_2399,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46245,c_46499])).

tff(c_46866,plain,(
    ! [A_2423,B_2424,C_2425] :
      ( k1_relset_1(A_2423,B_2424,C_2425) = k1_relat_1(C_2425)
      | ~ m1_subset_1(C_2425,k1_zfmisc_1(k2_zfmisc_1(A_2423,B_2424))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46895,plain,(
    ! [B_2426,A_2427] :
      ( k1_relset_1(B_2426,A_2427,'#skF_8') = k1_relat_1('#skF_8')
      | ~ v1_xboole_0(A_2427) ) ),
    inference(resolution,[status(thm)],[c_46433,c_46866])).

tff(c_46907,plain,(
    ! [B_2426] : k1_relset_1(B_2426,'#skF_8','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46245,c_46895])).

tff(c_47122,plain,(
    ! [A_2445,B_2446,C_2447] :
      ( m1_subset_1(k1_relset_1(A_2445,B_2446,C_2447),k1_zfmisc_1(A_2445))
      | ~ m1_subset_1(C_2447,k1_zfmisc_1(k2_zfmisc_1(A_2445,B_2446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_47153,plain,(
    ! [B_2426] :
      ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(B_2426))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_2426,'#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46907,c_47122])).

tff(c_47163,plain,(
    ! [B_2448] : m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(B_2448)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46538,c_46508,c_47153])).

tff(c_2,plain,(
    ! [C_4,B_2,A_1] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(B_2,A_1)))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46529,plain,(
    ! [C_4] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1('#skF_8'))
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46509,c_2])).

tff(c_46544,plain,(
    ! [C_4] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46245,c_46529])).

tff(c_47188,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_47163,c_46544])).

tff(c_47205,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_47188,c_46252])).

tff(c_47162,plain,(
    ! [B_2426] : m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(B_2426)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46538,c_46508,c_47153])).

tff(c_47234,plain,(
    ! [B_2450] : m1_subset_1('#skF_8',k1_zfmisc_1(B_2450)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47205,c_47162])).

tff(c_46,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_47241,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_47234,c_46])).

tff(c_47260,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47205,c_47241])).

tff(c_47207,plain,(
    ! [B_2426] : m1_subset_1('#skF_8',k1_zfmisc_1(B_2426)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47205,c_47162])).

tff(c_8,plain,(
    ! [C_7,B_6] :
      ( v1_funct_2(C_7,k1_xboole_0,B_6)
      | k1_relset_1(k1_xboole_0,B_6,C_7) != k1_xboole_0
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47523,plain,(
    ! [C_2476,B_2477] :
      ( v1_funct_2(C_2476,'#skF_8',B_2477)
      | k1_relset_1('#skF_8',B_2477,C_2476) != '#skF_8'
      | ~ m1_subset_1(C_2476,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_2477))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46249,c_46249,c_46249,c_46249,c_8])).

tff(c_47527,plain,(
    ! [B_2477] :
      ( v1_funct_2('#skF_8','#skF_8',B_2477)
      | k1_relset_1('#skF_8',B_2477,'#skF_8') != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_47207,c_47523])).

tff(c_47558,plain,(
    ! [B_2477] : v1_funct_2('#skF_8','#skF_8',B_2477) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47260,c_47527])).

tff(c_46282,plain,(
    ! [A_2354,B_2355] :
      ( r2_hidden(A_2354,B_2355)
      | v1_xboole_0(B_2355)
      | ~ m1_subset_1(A_2354,B_2355) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46290,plain,(
    ! [A_2354] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_2354,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46282,c_46244])).

tff(c_46293,plain,(
    ! [A_2356] : ~ m1_subset_1(A_2356,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46290])).

tff(c_46298,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_44,c_46293])).

tff(c_46299,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_46290])).

tff(c_46303,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46299,c_46252])).

tff(c_46312,plain,(
    ! [D_83] : ~ r2_hidden(D_83,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46303,c_46244])).

tff(c_46342,plain,(
    ! [B_2361] : r1_tarski('#skF_8',B_2361) ),
    inference(resolution,[status(thm)],[c_46330,c_46312])).

tff(c_46313,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46303,c_68])).

tff(c_48189,plain,(
    ! [A_2512,C_2513] :
      ( r2_hidden('#skF_5'(A_2512,k2_relat_1(A_2512),C_2513),k1_relat_1(A_2512))
      | ~ r2_hidden(C_2513,k2_relat_1(A_2512))
      | ~ v1_funct_1(A_2512)
      | ~ v1_relat_1(A_2512) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48213,plain,(
    ! [C_2513] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2513),'#skF_8')
      | ~ r2_hidden(C_2513,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46313,c_48189])).

tff(c_48223,plain,(
    ! [C_2513] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2513),'#skF_8')
      | ~ r2_hidden(C_2513,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_48213])).

tff(c_48225,plain,(
    ! [C_2514] : ~ r2_hidden(C_2514,k2_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_46312,c_48223])).

tff(c_48248,plain,(
    ! [B_2515] : r1_tarski(k2_relat_1('#skF_9'),B_2515) ),
    inference(resolution,[status(thm)],[c_20,c_48225])).

tff(c_46391,plain,(
    ! [A_66,A_2381,B_2380] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0(A_2381)
      | ~ r1_tarski(A_66,k2_zfmisc_1(B_2380,A_2381)) ) ),
    inference(resolution,[status(thm)],[c_54,c_46382])).

tff(c_46517,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0('#skF_8')
      | ~ r1_tarski(A_66,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46509,c_46391])).

tff(c_46536,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ r1_tarski(A_66,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46245,c_46517])).

tff(c_48290,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_48248,c_46536])).

tff(c_48309,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_48290,c_46252])).

tff(c_48340,plain,(
    ! [C_2516,A_2517,B_2518] :
      ( m1_subset_1(C_2516,k1_zfmisc_1(k2_zfmisc_1(A_2517,B_2518)))
      | ~ r1_tarski(k2_relat_1(C_2516),B_2518)
      | ~ r1_tarski(k1_relat_1(C_2516),A_2517)
      | ~ v1_relat_1(C_2516) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48396,plain,(
    ! [C_2519,B_2520] :
      ( m1_subset_1(C_2519,k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski(k2_relat_1(C_2519),'#skF_8')
      | ~ r1_tarski(k1_relat_1(C_2519),B_2520)
      | ~ v1_relat_1(C_2519) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46508,c_48340])).

tff(c_48398,plain,(
    ! [B_2520] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski('#skF_8','#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_2520)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48309,c_48396])).

tff(c_48403,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46342,c_46313,c_46343,c_48398])).

tff(c_48429,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_48403,c_46544])).

tff(c_48445,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_48429,c_46252])).

tff(c_46281,plain,(
    ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_46311,plain,(
    ~ v1_funct_2('#skF_9','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46303,c_46281])).

tff(c_48449,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48445,c_46311])).

tff(c_48457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47558,c_48449])).

tff(c_48458,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_48525,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48521,c_48458])).

tff(c_48713,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48712,c_48525])).

tff(c_48464,plain,(
    ! [A_2521,B_2522] :
      ( r2_hidden('#skF_1'(A_2521,B_2522),A_2521)
      | r1_tarski(A_2521,B_2522) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48472,plain,(
    ! [B_2522] : r1_tarski('#skF_7',B_2522) ),
    inference(resolution,[status(thm)],[c_48464,c_46244])).

tff(c_48524,plain,(
    ! [B_2522] : r1_tarski('#skF_8',B_2522) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48521,c_48472])).

tff(c_48528,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48521,c_68])).

tff(c_48527,plain,(
    ! [D_83] : ~ r2_hidden(D_83,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48521,c_46244])).

tff(c_50268,plain,(
    ! [A_2670,C_2671] :
      ( r2_hidden('#skF_5'(A_2670,k2_relat_1(A_2670),C_2671),k1_relat_1(A_2670))
      | ~ r2_hidden(C_2671,k2_relat_1(A_2670))
      | ~ v1_funct_1(A_2670)
      | ~ v1_relat_1(A_2670) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50292,plain,(
    ! [C_2671] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2671),'#skF_8')
      | ~ r2_hidden(C_2671,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48528,c_50268])).

tff(c_50302,plain,(
    ! [C_2671] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2671),'#skF_8')
      | ~ r2_hidden(C_2671,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_50292])).

tff(c_50304,plain,(
    ! [C_2672] : ~ r2_hidden(C_2672,k2_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_48527,c_50302])).

tff(c_50327,plain,(
    ! [B_2673] : r1_tarski(k2_relat_1('#skF_9'),B_2673) ),
    inference(resolution,[status(thm)],[c_20,c_50304])).

tff(c_48715,plain,(
    ! [B_2569] : k2_zfmisc_1(B_2569,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46245,c_48703])).

tff(c_48612,plain,(
    ! [A_66,A_2552,B_2551] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0(A_2552)
      | ~ r1_tarski(A_66,k2_zfmisc_1(B_2551,A_2552)) ) ),
    inference(resolution,[status(thm)],[c_54,c_48603])).

tff(c_48723,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0('#skF_8')
      | ~ r1_tarski(A_66,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48715,c_48612])).

tff(c_48742,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ r1_tarski(A_66,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46245,c_48723])).

tff(c_50369,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_50327,c_48742])).

tff(c_50388,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_50369,c_46252])).

tff(c_50463,plain,(
    ! [C_2678,A_2679,B_2680] :
      ( m1_subset_1(C_2678,k1_zfmisc_1(k2_zfmisc_1(A_2679,B_2680)))
      | ~ r1_tarski(k2_relat_1(C_2678),B_2680)
      | ~ r1_tarski(k1_relat_1(C_2678),A_2679)
      | ~ v1_relat_1(C_2678) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50655,plain,(
    ! [C_2688,B_2689] :
      ( m1_subset_1(C_2688,k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski(k2_relat_1(C_2688),'#skF_8')
      | ~ r1_tarski(k1_relat_1(C_2688),B_2689)
      | ~ v1_relat_1(C_2688) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48712,c_50463])).

tff(c_50660,plain,(
    ! [B_2689] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski('#skF_8','#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_2689)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50388,c_50655])).

tff(c_50666,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_48524,c_48528,c_48485,c_50660])).

tff(c_50668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48713,c_50666])).

%------------------------------------------------------------------------------
