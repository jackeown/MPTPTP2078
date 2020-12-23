%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:19 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 203 expanded)
%              Number of leaves         :   30 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 481 expanded)
%              Number of equality atoms :   27 (  81 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_51,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ! [B_35,A_34] :
      ( m1_subset_1(B_35,A_34)
      | ~ v1_xboole_0(B_35)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_127,plain,(
    ! [B_56,A_57] :
      ( r2_hidden(B_56,A_57)
      | ~ m1_subset_1(B_56,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,'#skF_9')
      | ~ m1_subset_1(C_37,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_137,plain,(
    ! [B_56] :
      ( ~ m1_subset_1(B_56,'#skF_8')
      | ~ m1_subset_1(B_56,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_127,c_60])).

tff(c_199,plain,(
    ! [B_68] :
      ( ~ m1_subset_1(B_68,'#skF_8')
      | ~ m1_subset_1(B_68,'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_204,plain,(
    ! [B_35] :
      ( ~ m1_subset_1(B_35,'#skF_8')
      | ~ v1_xboole_0(B_35)
      | ~ v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_199])).

tff(c_205,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_92,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_1'(A_47),A_47)
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_96,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_92,c_60])).

tff(c_99,plain,(
    ~ m1_subset_1('#skF_1'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_96])).

tff(c_8,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_161,plain,(
    ! [B_61,A_62] :
      ( m1_subset_1(B_61,A_62)
      | ~ r2_hidden(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_173,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1'(A_3),A_3)
      | v1_xboole_0(A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(resolution,[status(thm)],[c_8,c_161])).

tff(c_106,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,A_51)
      | ~ v1_xboole_0(B_50)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_114,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_9'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_106,c_99])).

tff(c_115,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_100,plain,(
    ! [B_48,A_49] :
      ( v1_xboole_0(B_48)
      | ~ m1_subset_1(B_48,A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_104,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_100])).

tff(c_105,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_20,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1526,plain,(
    ! [B_160,A_161] :
      ( r1_tarski(B_160,A_161)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_161))
      | v1_xboole_0(k1_zfmisc_1(A_161)) ) ),
    inference(resolution,[status(thm)],[c_127,c_20])).

tff(c_1540,plain,
    ( r1_tarski('#skF_9','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_1526])).

tff(c_1548,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1540])).

tff(c_54,plain,(
    ! [B_35,A_34] :
      ( r2_hidden(B_35,A_34)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_33] : k3_tarski(k1_zfmisc_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_187,plain,(
    ! [C_65,A_66,D_67] :
      ( r2_hidden(C_65,k3_tarski(A_66))
      | ~ r2_hidden(D_67,A_66)
      | ~ r2_hidden(C_65,D_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_191,plain,(
    ! [C_65,A_9,C_13] :
      ( r2_hidden(C_65,k3_tarski(k1_zfmisc_1(A_9)))
      | ~ r2_hidden(C_65,C_13)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_22,c_187])).

tff(c_1395,plain,(
    ! [C_146,A_147,C_148] :
      ( r2_hidden(C_146,A_147)
      | ~ r2_hidden(C_146,C_148)
      | ~ r1_tarski(C_148,A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191])).

tff(c_1738,plain,(
    ! [B_182,A_183,A_184] :
      ( r2_hidden(B_182,A_183)
      | ~ r1_tarski(A_184,A_183)
      | ~ m1_subset_1(B_182,A_184)
      | v1_xboole_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_54,c_1395])).

tff(c_1742,plain,(
    ! [B_182] :
      ( r2_hidden(B_182,'#skF_8')
      | ~ m1_subset_1(B_182,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1548,c_1738])).

tff(c_1765,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,'#skF_8')
      | ~ m1_subset_1(B_185,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_1742])).

tff(c_52,plain,(
    ! [B_35,A_34] :
      ( m1_subset_1(B_35,A_34)
      | ~ r2_hidden(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1772,plain,(
    ! [B_185] :
      ( m1_subset_1(B_185,'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(B_185,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1765,c_52])).

tff(c_1804,plain,(
    ! [B_188] :
      ( m1_subset_1(B_188,'#skF_8')
      | ~ m1_subset_1(B_188,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1772])).

tff(c_1808,plain,
    ( m1_subset_1('#skF_1'('#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_173,c_1804])).

tff(c_1816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_205,c_99,c_1808])).

tff(c_1818,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_18,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1821,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1818,c_18])).

tff(c_1825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1821])).

tff(c_1827,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_1831,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1827,c_18])).

tff(c_1836,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_62])).

tff(c_1922,plain,(
    ! [B_204,A_205] :
      ( r2_hidden(B_204,A_205)
      | ~ m1_subset_1(B_204,A_205)
      | v1_xboole_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2167,plain,(
    ! [B_229,A_230] :
      ( r1_tarski(B_229,A_230)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(A_230))
      | v1_xboole_0(k1_zfmisc_1(A_230)) ) ),
    inference(resolution,[status(thm)],[c_1922,c_20])).

tff(c_2184,plain,
    ( r1_tarski('#skF_9','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_2167])).

tff(c_2193,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_2184])).

tff(c_16,plain,(
    ! [A_7] :
      ( r2_xboole_0(k1_xboole_0,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ r2_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_7] :
      ( r1_tarski(k1_xboole_0,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_1833,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_8',A_7)
      | A_7 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_1831,c_89])).

tff(c_1890,plain,(
    ! [B_199,A_200] :
      ( B_199 = A_200
      | ~ r1_tarski(B_199,A_200)
      | ~ r1_tarski(A_200,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1895,plain,(
    ! [A_7] :
      ( ~ r1_tarski(A_7,'#skF_8')
      | A_7 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1833,c_1890])).

tff(c_2203,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2193,c_1895])).

tff(c_2209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1836,c_2203])).

tff(c_2210,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_2214,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2210,c_18])).

tff(c_2218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:41:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.70  
% 4.11/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.71  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 4.11/1.71  
% 4.11/1.71  %Foreground sorts:
% 4.11/1.71  
% 4.11/1.71  
% 4.11/1.71  %Background operators:
% 4.11/1.71  
% 4.11/1.71  
% 4.11/1.71  %Foreground operators:
% 4.11/1.71  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.11/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.11/1.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.11/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.71  tff('#skF_9', type, '#skF_9': $i).
% 4.11/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.11/1.71  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.11/1.71  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.11/1.71  tff('#skF_8', type, '#skF_8': $i).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.11/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.11/1.71  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.11/1.71  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.11/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.71  
% 4.11/1.72  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.11/1.72  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.11/1.72  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.11/1.72  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.11/1.72  tff(f_74, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.11/1.72  tff(f_72, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 4.11/1.72  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 4.11/1.72  tff(f_51, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 4.11/1.72  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.11/1.72  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.11/1.72  tff(c_62, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.11/1.72  tff(c_56, plain, (![B_35, A_34]: (m1_subset_1(B_35, A_34) | ~v1_xboole_0(B_35) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_127, plain, (![B_56, A_57]: (r2_hidden(B_56, A_57) | ~m1_subset_1(B_56, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_60, plain, (![C_37]: (~r2_hidden(C_37, '#skF_9') | ~m1_subset_1(C_37, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.11/1.72  tff(c_137, plain, (![B_56]: (~m1_subset_1(B_56, '#skF_8') | ~m1_subset_1(B_56, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_127, c_60])).
% 4.11/1.72  tff(c_199, plain, (![B_68]: (~m1_subset_1(B_68, '#skF_8') | ~m1_subset_1(B_68, '#skF_9'))), inference(splitLeft, [status(thm)], [c_137])).
% 4.11/1.72  tff(c_204, plain, (![B_35]: (~m1_subset_1(B_35, '#skF_8') | ~v1_xboole_0(B_35) | ~v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_199])).
% 4.11/1.72  tff(c_205, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_204])).
% 4.11/1.72  tff(c_92, plain, (![A_47]: (r2_hidden('#skF_1'(A_47), A_47) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.11/1.72  tff(c_96, plain, (~m1_subset_1('#skF_1'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_92, c_60])).
% 4.11/1.72  tff(c_99, plain, (~m1_subset_1('#skF_1'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_96])).
% 4.11/1.72  tff(c_8, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.11/1.72  tff(c_161, plain, (![B_61, A_62]: (m1_subset_1(B_61, A_62) | ~r2_hidden(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_173, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), A_3) | v1_xboole_0(A_3) | k1_xboole_0=A_3)), inference(resolution, [status(thm)], [c_8, c_161])).
% 4.11/1.72  tff(c_106, plain, (![B_50, A_51]: (m1_subset_1(B_50, A_51) | ~v1_xboole_0(B_50) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_114, plain, (~v1_xboole_0('#skF_1'('#skF_9')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_106, c_99])).
% 4.11/1.72  tff(c_115, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_114])).
% 4.11/1.72  tff(c_64, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.11/1.72  tff(c_100, plain, (![B_48, A_49]: (v1_xboole_0(B_48) | ~m1_subset_1(B_48, A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_104, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_100])).
% 4.11/1.72  tff(c_105, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_104])).
% 4.11/1.72  tff(c_20, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.72  tff(c_1526, plain, (![B_160, A_161]: (r1_tarski(B_160, A_161) | ~m1_subset_1(B_160, k1_zfmisc_1(A_161)) | v1_xboole_0(k1_zfmisc_1(A_161)))), inference(resolution, [status(thm)], [c_127, c_20])).
% 4.11/1.72  tff(c_1540, plain, (r1_tarski('#skF_9', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_1526])).
% 4.11/1.72  tff(c_1548, plain, (r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_105, c_1540])).
% 4.11/1.72  tff(c_54, plain, (![B_35, A_34]: (r2_hidden(B_35, A_34) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_50, plain, (![A_33]: (k3_tarski(k1_zfmisc_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.11/1.72  tff(c_22, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.72  tff(c_187, plain, (![C_65, A_66, D_67]: (r2_hidden(C_65, k3_tarski(A_66)) | ~r2_hidden(D_67, A_66) | ~r2_hidden(C_65, D_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.11/1.72  tff(c_191, plain, (![C_65, A_9, C_13]: (r2_hidden(C_65, k3_tarski(k1_zfmisc_1(A_9))) | ~r2_hidden(C_65, C_13) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_22, c_187])).
% 4.11/1.72  tff(c_1395, plain, (![C_146, A_147, C_148]: (r2_hidden(C_146, A_147) | ~r2_hidden(C_146, C_148) | ~r1_tarski(C_148, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191])).
% 4.11/1.72  tff(c_1738, plain, (![B_182, A_183, A_184]: (r2_hidden(B_182, A_183) | ~r1_tarski(A_184, A_183) | ~m1_subset_1(B_182, A_184) | v1_xboole_0(A_184))), inference(resolution, [status(thm)], [c_54, c_1395])).
% 4.11/1.72  tff(c_1742, plain, (![B_182]: (r2_hidden(B_182, '#skF_8') | ~m1_subset_1(B_182, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_1548, c_1738])).
% 4.11/1.72  tff(c_1765, plain, (![B_185]: (r2_hidden(B_185, '#skF_8') | ~m1_subset_1(B_185, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_205, c_1742])).
% 4.11/1.72  tff(c_52, plain, (![B_35, A_34]: (m1_subset_1(B_35, A_34) | ~r2_hidden(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_1772, plain, (![B_185]: (m1_subset_1(B_185, '#skF_8') | v1_xboole_0('#skF_8') | ~m1_subset_1(B_185, '#skF_9'))), inference(resolution, [status(thm)], [c_1765, c_52])).
% 4.11/1.72  tff(c_1804, plain, (![B_188]: (m1_subset_1(B_188, '#skF_8') | ~m1_subset_1(B_188, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_115, c_1772])).
% 4.11/1.72  tff(c_1808, plain, (m1_subset_1('#skF_1'('#skF_9'), '#skF_8') | v1_xboole_0('#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_173, c_1804])).
% 4.11/1.72  tff(c_1816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_205, c_99, c_1808])).
% 4.11/1.72  tff(c_1818, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_204])).
% 4.11/1.72  tff(c_18, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.11/1.72  tff(c_1821, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1818, c_18])).
% 4.11/1.72  tff(c_1825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1821])).
% 4.11/1.72  tff(c_1827, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_114])).
% 4.11/1.72  tff(c_1831, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1827, c_18])).
% 4.11/1.72  tff(c_1836, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_62])).
% 4.11/1.72  tff(c_1922, plain, (![B_204, A_205]: (r2_hidden(B_204, A_205) | ~m1_subset_1(B_204, A_205) | v1_xboole_0(A_205))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.72  tff(c_2167, plain, (![B_229, A_230]: (r1_tarski(B_229, A_230) | ~m1_subset_1(B_229, k1_zfmisc_1(A_230)) | v1_xboole_0(k1_zfmisc_1(A_230)))), inference(resolution, [status(thm)], [c_1922, c_20])).
% 4.11/1.72  tff(c_2184, plain, (r1_tarski('#skF_9', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_2167])).
% 4.11/1.72  tff(c_2193, plain, (r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_105, c_2184])).
% 4.11/1.72  tff(c_16, plain, (![A_7]: (r2_xboole_0(k1_xboole_0, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.11/1.72  tff(c_85, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~r2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.72  tff(c_89, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7) | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_16, c_85])).
% 4.11/1.72  tff(c_1833, plain, (![A_7]: (r1_tarski('#skF_8', A_7) | A_7='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_1831, c_89])).
% 4.11/1.72  tff(c_1890, plain, (![B_199, A_200]: (B_199=A_200 | ~r1_tarski(B_199, A_200) | ~r1_tarski(A_200, B_199))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.72  tff(c_1895, plain, (![A_7]: (~r1_tarski(A_7, '#skF_8') | A_7='#skF_8')), inference(resolution, [status(thm)], [c_1833, c_1890])).
% 4.11/1.72  tff(c_2203, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_2193, c_1895])).
% 4.11/1.72  tff(c_2209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1836, c_2203])).
% 4.11/1.72  tff(c_2210, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_104])).
% 4.11/1.72  tff(c_2214, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2210, c_18])).
% 4.11/1.72  tff(c_2218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2214])).
% 4.11/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.72  
% 4.11/1.72  Inference rules
% 4.11/1.72  ----------------------
% 4.11/1.72  #Ref     : 0
% 4.11/1.72  #Sup     : 456
% 4.11/1.72  #Fact    : 0
% 4.11/1.72  #Define  : 0
% 4.11/1.72  #Split   : 17
% 4.11/1.72  #Chain   : 0
% 4.11/1.72  #Close   : 0
% 4.11/1.72  
% 4.11/1.72  Ordering : KBO
% 4.11/1.72  
% 4.11/1.72  Simplification rules
% 4.11/1.72  ----------------------
% 4.11/1.72  #Subsume      : 62
% 4.11/1.72  #Demod        : 136
% 4.11/1.72  #Tautology    : 116
% 4.11/1.72  #SimpNegUnit  : 43
% 4.11/1.72  #BackRed      : 9
% 4.11/1.72  
% 4.11/1.72  #Partial instantiations: 0
% 4.11/1.72  #Strategies tried      : 1
% 4.11/1.72  
% 4.11/1.72  Timing (in seconds)
% 4.11/1.72  ----------------------
% 4.11/1.73  Preprocessing        : 0.32
% 4.11/1.73  Parsing              : 0.17
% 4.11/1.73  CNF conversion       : 0.03
% 4.11/1.73  Main loop            : 0.65
% 4.11/1.73  Inferencing          : 0.23
% 4.11/1.73  Reduction            : 0.18
% 4.11/1.73  Demodulation         : 0.11
% 4.11/1.73  BG Simplification    : 0.03
% 4.11/1.73  Subsumption          : 0.15
% 4.11/1.73  Abstraction          : 0.03
% 4.11/1.73  MUC search           : 0.00
% 4.11/1.73  Cooper               : 0.00
% 4.11/1.73  Total                : 1.01
% 4.11/1.73  Index Insertion      : 0.00
% 4.11/1.73  Index Deletion       : 0.00
% 4.11/1.73  Index Matching       : 0.00
% 4.11/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
