%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 107 expanded)
%              Number of leaves         :   48 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 173 expanded)
%              Number of equality atoms :   43 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_80,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_82,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k1_xboole_0
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_106] : k4_xboole_0(k1_xboole_0,A_106) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_26,plain,(
    ! [C_35,B_34] : ~ r2_hidden(C_35,k4_xboole_0(B_34,k1_tarski(C_35))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_133,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_26])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_163,plain,(
    ! [B_113,C_114,A_115] :
      ( r2_hidden(B_113,C_114)
      | k4_xboole_0(k2_tarski(A_115,B_113),C_114) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_170,plain,(
    ! [B_113,A_115] :
      ( r2_hidden(B_113,k1_xboole_0)
      | k2_tarski(A_115,B_113) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_163])).

tff(c_172,plain,(
    ! [A_116,B_117] : k2_tarski(A_116,B_117) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_170])).

tff(c_174,plain,(
    ! [A_5] : k1_tarski(A_5) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_172])).

tff(c_86,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_416,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_420,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_416])).

tff(c_761,plain,(
    ! [B_236,A_237,C_238] :
      ( k1_xboole_0 = B_236
      | k1_relset_1(A_237,B_236,C_238) = A_237
      | ~ v1_funct_2(C_238,A_237,B_236)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_764,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_761])).

tff(c_767,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_420,c_764])).

tff(c_768,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_767])).

tff(c_158,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_162,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_158])).

tff(c_88,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_193,plain,(
    ! [C_127,B_128,A_129] :
      ( v5_relat_1(C_127,B_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_197,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_193])).

tff(c_464,plain,(
    ! [A_179,D_180] :
      ( r2_hidden(k1_funct_1(A_179,D_180),k2_relat_1(A_179))
      | ~ r2_hidden(D_180,k1_relat_1(A_179))
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_213,plain,(
    ! [B_135,A_136] :
      ( r1_tarski(k2_relat_1(B_135),A_136)
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_221,plain,(
    ! [B_135,A_136] :
      ( k4_xboole_0(k2_relat_1(B_135),A_136) = k1_xboole_0
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_213,c_4])).

tff(c_280,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(A_150,k4_xboole_0(B_151,k1_tarski(C_152)))
      | C_152 = A_150
      | ~ r2_hidden(A_150,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_294,plain,(
    ! [A_150,C_152,B_135] :
      ( r2_hidden(A_150,k1_xboole_0)
      | C_152 = A_150
      | ~ r2_hidden(A_150,k2_relat_1(B_135))
      | ~ v5_relat_1(B_135,k1_tarski(C_152))
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_280])).

tff(c_303,plain,(
    ! [C_152,A_150,B_135] :
      ( C_152 = A_150
      | ~ r2_hidden(A_150,k2_relat_1(B_135))
      | ~ v5_relat_1(B_135,k1_tarski(C_152))
      | ~ v1_relat_1(B_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_294])).

tff(c_556,plain,(
    ! [A_211,D_212,C_213] :
      ( k1_funct_1(A_211,D_212) = C_213
      | ~ v5_relat_1(A_211,k1_tarski(C_213))
      | ~ r2_hidden(D_212,k1_relat_1(A_211))
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_464,c_303])).

tff(c_558,plain,(
    ! [D_212] :
      ( k1_funct_1('#skF_8',D_212) = '#skF_6'
      | ~ r2_hidden(D_212,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_197,c_556])).

tff(c_561,plain,(
    ! [D_212] :
      ( k1_funct_1('#skF_8',D_212) = '#skF_6'
      | ~ r2_hidden(D_212,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_88,c_558])).

tff(c_789,plain,(
    ! [D_239] :
      ( k1_funct_1('#skF_8',D_239) = '#skF_6'
      | ~ r2_hidden(D_239,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_561])).

tff(c_792,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_82,c_789])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 3.15/1.46  
% 3.15/1.46  %Foreground sorts:
% 3.15/1.46  
% 3.15/1.46  
% 3.15/1.46  %Background operators:
% 3.15/1.46  
% 3.15/1.46  
% 3.15/1.46  %Foreground operators:
% 3.15/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.15/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.15/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.15/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.15/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.46  tff('#skF_8', type, '#skF_8': $i).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.15/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.46  
% 3.15/1.47  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.15/1.47  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.15/1.47  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.47  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.15/1.47  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.15/1.47  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.47  tff(f_60, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 3.15/1.47  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.15/1.47  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.15/1.47  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.15/1.47  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.15/1.47  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.15/1.47  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.15/1.47  tff(c_80, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.15/1.47  tff(c_82, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.15/1.47  tff(c_10, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.47  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.47  tff(c_119, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k1_xboole_0 | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.47  tff(c_128, plain, (![A_106]: (k4_xboole_0(k1_xboole_0, A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_119])).
% 3.15/1.47  tff(c_26, plain, (![C_35, B_34]: (~r2_hidden(C_35, k4_xboole_0(B_34, k1_tarski(C_35))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.47  tff(c_133, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_26])).
% 3.15/1.47  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.47  tff(c_163, plain, (![B_113, C_114, A_115]: (r2_hidden(B_113, C_114) | k4_xboole_0(k2_tarski(A_115, B_113), C_114)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.47  tff(c_170, plain, (![B_113, A_115]: (r2_hidden(B_113, k1_xboole_0) | k2_tarski(A_115, B_113)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_163])).
% 3.15/1.47  tff(c_172, plain, (![A_116, B_117]: (k2_tarski(A_116, B_117)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_133, c_170])).
% 3.15/1.47  tff(c_174, plain, (![A_5]: (k1_tarski(A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_172])).
% 3.15/1.47  tff(c_86, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.15/1.47  tff(c_84, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.15/1.47  tff(c_416, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.47  tff(c_420, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_84, c_416])).
% 3.15/1.47  tff(c_761, plain, (![B_236, A_237, C_238]: (k1_xboole_0=B_236 | k1_relset_1(A_237, B_236, C_238)=A_237 | ~v1_funct_2(C_238, A_237, B_236) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.47  tff(c_764, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_761])).
% 3.15/1.47  tff(c_767, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_420, c_764])).
% 3.15/1.47  tff(c_768, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_174, c_767])).
% 3.15/1.47  tff(c_158, plain, (![C_110, A_111, B_112]: (v1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.47  tff(c_162, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_84, c_158])).
% 3.15/1.47  tff(c_88, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.15/1.47  tff(c_193, plain, (![C_127, B_128, A_129]: (v5_relat_1(C_127, B_128) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.15/1.47  tff(c_197, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_193])).
% 3.15/1.47  tff(c_464, plain, (![A_179, D_180]: (r2_hidden(k1_funct_1(A_179, D_180), k2_relat_1(A_179)) | ~r2_hidden(D_180, k1_relat_1(A_179)) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.15/1.47  tff(c_213, plain, (![B_135, A_136]: (r1_tarski(k2_relat_1(B_135), A_136) | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.47  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.47  tff(c_221, plain, (![B_135, A_136]: (k4_xboole_0(k2_relat_1(B_135), A_136)=k1_xboole_0 | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_213, c_4])).
% 3.15/1.47  tff(c_280, plain, (![A_150, B_151, C_152]: (r2_hidden(A_150, k4_xboole_0(B_151, k1_tarski(C_152))) | C_152=A_150 | ~r2_hidden(A_150, B_151))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.47  tff(c_294, plain, (![A_150, C_152, B_135]: (r2_hidden(A_150, k1_xboole_0) | C_152=A_150 | ~r2_hidden(A_150, k2_relat_1(B_135)) | ~v5_relat_1(B_135, k1_tarski(C_152)) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_221, c_280])).
% 3.15/1.47  tff(c_303, plain, (![C_152, A_150, B_135]: (C_152=A_150 | ~r2_hidden(A_150, k2_relat_1(B_135)) | ~v5_relat_1(B_135, k1_tarski(C_152)) | ~v1_relat_1(B_135))), inference(negUnitSimplification, [status(thm)], [c_133, c_294])).
% 3.15/1.47  tff(c_556, plain, (![A_211, D_212, C_213]: (k1_funct_1(A_211, D_212)=C_213 | ~v5_relat_1(A_211, k1_tarski(C_213)) | ~r2_hidden(D_212, k1_relat_1(A_211)) | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_464, c_303])).
% 3.15/1.47  tff(c_558, plain, (![D_212]: (k1_funct_1('#skF_8', D_212)='#skF_6' | ~r2_hidden(D_212, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_197, c_556])).
% 3.15/1.47  tff(c_561, plain, (![D_212]: (k1_funct_1('#skF_8', D_212)='#skF_6' | ~r2_hidden(D_212, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_88, c_558])).
% 3.15/1.47  tff(c_789, plain, (![D_239]: (k1_funct_1('#skF_8', D_239)='#skF_6' | ~r2_hidden(D_239, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_561])).
% 3.15/1.47  tff(c_792, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_82, c_789])).
% 3.15/1.47  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_792])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 144
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 3
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 48
% 3.15/1.47  #Demod        : 53
% 3.15/1.47  #Tautology    : 51
% 3.15/1.47  #SimpNegUnit  : 17
% 3.15/1.47  #BackRed      : 5
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.48  Preprocessing        : 0.36
% 3.15/1.48  Parsing              : 0.18
% 3.15/1.48  CNF conversion       : 0.03
% 3.15/1.48  Main loop            : 0.33
% 3.15/1.48  Inferencing          : 0.12
% 3.15/1.48  Reduction            : 0.10
% 3.15/1.48  Demodulation         : 0.07
% 3.15/1.48  BG Simplification    : 0.02
% 3.15/1.48  Subsumption          : 0.06
% 3.15/1.48  Abstraction          : 0.02
% 3.15/1.48  MUC search           : 0.00
% 3.15/1.48  Cooper               : 0.00
% 3.15/1.48  Total                : 0.73
% 3.15/1.48  Index Insertion      : 0.00
% 3.15/1.48  Index Deletion       : 0.00
% 3.15/1.48  Index Matching       : 0.00
% 3.15/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
