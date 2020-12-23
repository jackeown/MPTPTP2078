%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:21 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 230 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 516 expanded)
%              Number of equality atoms :   14 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_94,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_167,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(B_61,A_62)
      | ~ m1_subset_1(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_175,plain,(
    ! [B_61,A_18] :
      ( r1_tarski(B_61,A_18)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_167,c_20])).

tff(c_197,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_175])).

tff(c_206,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_197])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_210,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_206,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_152,plain,(
    ! [A_54,B_55] :
      ( ~ r1_xboole_0(A_54,B_55)
      | v1_xboole_0(k3_xboole_0(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_214,plain,
    ( ~ r1_xboole_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_152])).

tff(c_221,plain,(
    ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ v1_xboole_0(B_43)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    ! [C_33] :
      ( ~ r2_hidden(C_33,'#skF_7')
      | ~ m1_subset_1(C_33,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_61,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_98,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_61])).

tff(c_115,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_230,plain,(
    ! [B_69,A_70] :
      ( m1_subset_1(B_69,A_70)
      | ~ r2_hidden(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1377,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1('#skF_2'(A_159,B_160),A_159)
      | v1_xboole_0(A_159)
      | r1_xboole_0(A_159,B_160) ) ),
    inference(resolution,[status(thm)],[c_12,c_230])).

tff(c_99,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),B_46)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [C_27] :
      ( ~ r2_hidden(C_27,'#skF_7')
      | ~ m1_subset_1(C_27,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_112,plain,(
    ! [A_45] :
      ( ~ m1_subset_1('#skF_2'(A_45,'#skF_7'),'#skF_6')
      | r1_xboole_0(A_45,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_99,c_42])).

tff(c_1389,plain,
    ( v1_xboole_0('#skF_6')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1377,c_112])).

tff(c_1400,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1389])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1443,plain,(
    ! [C_161] :
      ( ~ r2_hidden(C_161,'#skF_7')
      | ~ r2_hidden(C_161,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1400,c_8])).

tff(c_1535,plain,(
    ! [B_164] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_164),'#skF_6')
      | r1_xboole_0('#skF_7',B_164) ) ),
    inference(resolution,[status(thm)],[c_12,c_1443])).

tff(c_1542,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_1535])).

tff(c_1548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_221,c_1542])).

tff(c_1549,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1580,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1549,c_6])).

tff(c_1586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1580])).

tff(c_1588,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_1592,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1588,c_6])).

tff(c_1594,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_44])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,A_23)
      | ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1605,plain,(
    ! [B_168,A_169] :
      ( r2_hidden(B_168,A_169)
      | ~ m1_subset_1(B_168,A_169)
      | v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1620,plain,(
    ! [B_168] :
      ( ~ m1_subset_1(B_168,'#skF_6')
      | ~ m1_subset_1(B_168,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1605,c_42])).

tff(c_1692,plain,(
    ! [B_179] :
      ( ~ m1_subset_1(B_179,'#skF_6')
      | ~ m1_subset_1(B_179,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_1620])).

tff(c_1702,plain,(
    ! [B_24] :
      ( ~ m1_subset_1(B_24,'#skF_6')
      | ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_36,c_1692])).

tff(c_1712,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1702])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_46,A_45] :
      ( ~ v1_xboole_0(B_46)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_1609,plain,(
    ! [B_168,A_18] :
      ( r1_tarski(B_168,A_18)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_1605,c_20])).

tff(c_1622,plain,(
    ! [B_170,A_171] :
      ( r1_tarski(B_170,A_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_171)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1609])).

tff(c_1631,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_1622])).

tff(c_1635,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1631,c_18])).

tff(c_1713,plain,(
    ! [A_182,B_183,C_184] :
      ( ~ r1_xboole_0(A_182,B_183)
      | ~ r2_hidden(C_184,k3_xboole_0(A_182,B_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1716,plain,(
    ! [C_184] :
      ( ~ r1_xboole_0('#skF_7','#skF_6')
      | ~ r2_hidden(C_184,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_1713])).

tff(c_1737,plain,(
    ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1716])).

tff(c_1743,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_1737])).

tff(c_1748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1743])).

tff(c_1751,plain,(
    ! [C_185] : ~ r2_hidden(C_185,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1716])).

tff(c_1767,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_1751])).

tff(c_1776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1712,c_1767])).

tff(c_1778,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1702])).

tff(c_1593,plain,(
    ! [A_5] :
      ( A_5 = '#skF_6'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_6])).

tff(c_1788,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1778,c_1593])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1594,c_1788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:01:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.69  
% 3.56/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 3.56/1.69  
% 3.56/1.69  %Foreground sorts:
% 3.56/1.69  
% 3.56/1.69  
% 3.56/1.69  %Background operators:
% 3.56/1.69  
% 3.56/1.69  
% 3.56/1.69  %Foreground operators:
% 3.56/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.56/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.56/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.56/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.56/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.56/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.56/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.56/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.56/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.56/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.69  
% 3.56/1.71  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.56/1.71  tff(f_94, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.56/1.71  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.56/1.71  tff(f_78, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.56/1.71  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.56/1.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.56/1.71  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.56/1.71  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.56/1.71  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.56/1.71  tff(c_44, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.71  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.71  tff(c_40, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.56/1.71  tff(c_167, plain, (![B_61, A_62]: (r2_hidden(B_61, A_62) | ~m1_subset_1(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.71  tff(c_20, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.56/1.71  tff(c_175, plain, (![B_61, A_18]: (r1_tarski(B_61, A_18) | ~m1_subset_1(B_61, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_167, c_20])).
% 3.56/1.71  tff(c_197, plain, (![B_67, A_68]: (r1_tarski(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)))), inference(negUnitSimplification, [status(thm)], [c_40, c_175])).
% 3.56/1.71  tff(c_206, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_197])).
% 3.56/1.71  tff(c_18, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.56/1.71  tff(c_210, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_206, c_18])).
% 3.56/1.71  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.71  tff(c_137, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.71  tff(c_152, plain, (![A_54, B_55]: (~r1_xboole_0(A_54, B_55) | v1_xboole_0(k3_xboole_0(A_54, B_55)))), inference(resolution, [status(thm)], [c_4, c_137])).
% 3.56/1.71  tff(c_214, plain, (~r1_xboole_0('#skF_7', '#skF_6') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_210, c_152])).
% 3.56/1.71  tff(c_221, plain, (~r1_xboole_0('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_214])).
% 3.56/1.71  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.56/1.71  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.56/1.71  tff(c_90, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~v1_xboole_0(B_43) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.71  tff(c_55, plain, (![C_33]: (~r2_hidden(C_33, '#skF_7') | ~m1_subset_1(C_33, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.71  tff(c_60, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_55])).
% 3.56/1.71  tff(c_61, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_60])).
% 3.56/1.71  tff(c_98, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_90, c_61])).
% 3.56/1.71  tff(c_115, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_98])).
% 3.56/1.71  tff(c_230, plain, (![B_69, A_70]: (m1_subset_1(B_69, A_70) | ~r2_hidden(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.71  tff(c_1377, plain, (![A_159, B_160]: (m1_subset_1('#skF_2'(A_159, B_160), A_159) | v1_xboole_0(A_159) | r1_xboole_0(A_159, B_160))), inference(resolution, [status(thm)], [c_12, c_230])).
% 3.56/1.71  tff(c_99, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), B_46) | r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.56/1.71  tff(c_42, plain, (![C_27]: (~r2_hidden(C_27, '#skF_7') | ~m1_subset_1(C_27, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.56/1.71  tff(c_112, plain, (![A_45]: (~m1_subset_1('#skF_2'(A_45, '#skF_7'), '#skF_6') | r1_xboole_0(A_45, '#skF_7'))), inference(resolution, [status(thm)], [c_99, c_42])).
% 3.56/1.71  tff(c_1389, plain, (v1_xboole_0('#skF_6') | r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_1377, c_112])).
% 3.56/1.71  tff(c_1400, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_115, c_1389])).
% 3.56/1.71  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.56/1.71  tff(c_1443, plain, (![C_161]: (~r2_hidden(C_161, '#skF_7') | ~r2_hidden(C_161, '#skF_6'))), inference(resolution, [status(thm)], [c_1400, c_8])).
% 3.56/1.71  tff(c_1535, plain, (![B_164]: (~r2_hidden('#skF_2'('#skF_7', B_164), '#skF_6') | r1_xboole_0('#skF_7', B_164))), inference(resolution, [status(thm)], [c_12, c_1443])).
% 3.56/1.71  tff(c_1542, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_10, c_1535])).
% 3.56/1.71  tff(c_1548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_221, c_1542])).
% 3.56/1.71  tff(c_1549, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_214])).
% 3.56/1.71  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.71  tff(c_1580, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1549, c_6])).
% 3.56/1.71  tff(c_1586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1580])).
% 3.56/1.71  tff(c_1588, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_98])).
% 3.56/1.71  tff(c_1592, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1588, c_6])).
% 3.56/1.71  tff(c_1594, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_44])).
% 3.56/1.71  tff(c_36, plain, (![B_24, A_23]: (m1_subset_1(B_24, A_23) | ~v1_xboole_0(B_24) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.71  tff(c_1605, plain, (![B_168, A_169]: (r2_hidden(B_168, A_169) | ~m1_subset_1(B_168, A_169) | v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.71  tff(c_1620, plain, (![B_168]: (~m1_subset_1(B_168, '#skF_6') | ~m1_subset_1(B_168, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_1605, c_42])).
% 3.56/1.71  tff(c_1692, plain, (![B_179]: (~m1_subset_1(B_179, '#skF_6') | ~m1_subset_1(B_179, '#skF_7'))), inference(splitLeft, [status(thm)], [c_1620])).
% 3.56/1.71  tff(c_1702, plain, (![B_24]: (~m1_subset_1(B_24, '#skF_6') | ~v1_xboole_0(B_24) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_36, c_1692])).
% 3.56/1.71  tff(c_1712, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1702])).
% 3.56/1.71  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.71  tff(c_113, plain, (![B_46, A_45]: (~v1_xboole_0(B_46) | r1_xboole_0(A_45, B_46))), inference(resolution, [status(thm)], [c_99, c_2])).
% 3.56/1.71  tff(c_1609, plain, (![B_168, A_18]: (r1_tarski(B_168, A_18) | ~m1_subset_1(B_168, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_1605, c_20])).
% 3.56/1.71  tff(c_1622, plain, (![B_170, A_171]: (r1_tarski(B_170, A_171) | ~m1_subset_1(B_170, k1_zfmisc_1(A_171)))), inference(negUnitSimplification, [status(thm)], [c_40, c_1609])).
% 3.56/1.71  tff(c_1631, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_1622])).
% 3.56/1.71  tff(c_1635, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_1631, c_18])).
% 3.56/1.71  tff(c_1713, plain, (![A_182, B_183, C_184]: (~r1_xboole_0(A_182, B_183) | ~r2_hidden(C_184, k3_xboole_0(A_182, B_183)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.71  tff(c_1716, plain, (![C_184]: (~r1_xboole_0('#skF_7', '#skF_6') | ~r2_hidden(C_184, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1635, c_1713])).
% 3.56/1.71  tff(c_1737, plain, (~r1_xboole_0('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_1716])).
% 3.56/1.71  tff(c_1743, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_113, c_1737])).
% 3.56/1.71  tff(c_1748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1743])).
% 3.56/1.71  tff(c_1751, plain, (![C_185]: (~r2_hidden(C_185, '#skF_7'))), inference(splitRight, [status(thm)], [c_1716])).
% 3.56/1.71  tff(c_1767, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_1751])).
% 3.56/1.71  tff(c_1776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1712, c_1767])).
% 3.56/1.71  tff(c_1778, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1702])).
% 3.56/1.71  tff(c_1593, plain, (![A_5]: (A_5='#skF_6' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_6])).
% 3.56/1.71  tff(c_1788, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1778, c_1593])).
% 3.56/1.71  tff(c_1792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1594, c_1788])).
% 3.56/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.71  
% 3.56/1.71  Inference rules
% 3.56/1.71  ----------------------
% 3.56/1.71  #Ref     : 0
% 3.56/1.71  #Sup     : 370
% 3.56/1.71  #Fact    : 0
% 3.56/1.71  #Define  : 0
% 3.56/1.71  #Split   : 8
% 3.56/1.71  #Chain   : 0
% 3.56/1.71  #Close   : 0
% 3.56/1.71  
% 3.56/1.71  Ordering : KBO
% 3.56/1.71  
% 3.56/1.71  Simplification rules
% 3.56/1.71  ----------------------
% 3.56/1.71  #Subsume      : 116
% 3.56/1.71  #Demod        : 115
% 3.56/1.71  #Tautology    : 127
% 3.56/1.71  #SimpNegUnit  : 61
% 3.56/1.71  #BackRed      : 14
% 3.56/1.71  
% 3.56/1.71  #Partial instantiations: 0
% 3.56/1.71  #Strategies tried      : 1
% 3.56/1.71  
% 3.56/1.71  Timing (in seconds)
% 3.56/1.71  ----------------------
% 3.56/1.72  Preprocessing        : 0.40
% 3.56/1.72  Parsing              : 0.21
% 3.56/1.72  CNF conversion       : 0.03
% 3.56/1.72  Main loop            : 0.48
% 3.56/1.72  Inferencing          : 0.18
% 3.56/1.72  Reduction            : 0.13
% 3.56/1.72  Demodulation         : 0.08
% 3.56/1.72  BG Simplification    : 0.03
% 3.56/1.72  Subsumption          : 0.09
% 3.56/1.72  Abstraction          : 0.02
% 3.56/1.72  MUC search           : 0.00
% 3.56/1.72  Cooper               : 0.00
% 3.56/1.72  Total                : 0.92
% 3.56/1.72  Index Insertion      : 0.00
% 3.56/1.72  Index Deletion       : 0.00
% 3.56/1.72  Index Matching       : 0.00
% 3.56/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
