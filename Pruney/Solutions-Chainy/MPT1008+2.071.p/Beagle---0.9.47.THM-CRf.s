%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:35 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 426 expanded)
%              Number of leaves         :   61 ( 174 expanded)
%              Depth                    :   19
%              Number of atoms          :  198 ( 901 expanded)
%              Number of equality atoms :   73 ( 331 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_17 > #skF_6 > #skF_15 > #skF_9 > #skF_3 > #skF_16 > #skF_12 > #skF_10 > #skF_7 > #skF_2 > #skF_8 > #skF_14 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_265,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_222,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_189,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_226,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_140,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_137,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_154,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_218,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_210,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_253,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_294,plain,(
    ! [A_183,B_184,C_185] :
      ( ~ r1_xboole_0(A_183,B_184)
      | ~ r2_hidden(C_185,k3_xboole_0(A_183,B_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_297,plain,(
    ! [A_8,C_185] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_185,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_294])).

tff(c_298,plain,(
    ! [C_185] : ~ r2_hidden(C_185,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_146,plain,(
    m1_subset_1('#skF_17',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_15'),'#skF_16'))) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_311,plain,(
    ! [C_189,A_190,B_191] :
      ( v1_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_324,plain,(
    v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_146,c_311])).

tff(c_150,plain,(
    v1_funct_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_108,plain,(
    ! [A_92,B_95] :
      ( k1_funct_1(A_92,B_95) = k1_xboole_0
      | r2_hidden(B_95,k1_relat_1(A_92))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_980,plain,(
    ! [A_247,B_248,C_249] :
      ( k2_relset_1(A_247,B_248,C_249) = k2_relat_1(C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_995,plain,(
    k2_relset_1(k1_tarski('#skF_15'),'#skF_16','#skF_17') = k2_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_146,c_980])).

tff(c_142,plain,(
    k2_relset_1(k1_tarski('#skF_15'),'#skF_16','#skF_17') != k1_tarski(k1_funct_1('#skF_17','#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_1009,plain,(
    k1_tarski(k1_funct_1('#skF_17','#skF_15')) != k2_relat_1('#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_142])).

tff(c_28,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_190,plain,(
    ! [A_161,B_162] : v1_relat_1(k2_zfmisc_1(A_161,B_162)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_192,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_190])).

tff(c_70,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_48,plain,(
    ! [A_27] : k7_relat_1(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_519,plain,(
    ! [B_212,A_213] :
      ( k3_xboole_0(k1_relat_1(B_212),A_213) = k1_relat_1(k7_relat_1(B_212,A_213))
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_546,plain,(
    ! [A_213] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_213)) = k3_xboole_0(k1_xboole_0,A_213)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_519])).

tff(c_553,plain,(
    ! [A_214] : k3_xboole_0(k1_xboole_0,A_214) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_70,c_48,c_546])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | k3_xboole_0(A_18,k1_tarski(B_19)) != k1_tarski(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_559,plain,(
    ! [B_19] :
      ( r2_hidden(B_19,k1_xboole_0)
      | k1_tarski(B_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_36])).

tff(c_572,plain,(
    ! [B_19] : k1_tarski(B_19) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_559])).

tff(c_144,plain,(
    k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_285,plain,(
    ! [A_181,B_182] :
      ( r1_tarski(A_181,B_182)
      | ~ m1_subset_1(A_181,k1_zfmisc_1(B_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_293,plain,(
    r1_tarski('#skF_17',k2_zfmisc_1(k1_tarski('#skF_15'),'#skF_16')) ),
    inference(resolution,[status(thm)],[c_146,c_285])).

tff(c_44,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    ! [A_36,B_37] :
      ( k1_relat_1(k2_zfmisc_1(A_36,B_37)) = A_36
      | k1_xboole_0 = B_37
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_753,plain,(
    ! [A_229,B_230] :
      ( r1_tarski(k1_relat_1(A_229),k1_relat_1(B_230))
      | ~ r1_tarski(A_229,B_230)
      | ~ v1_relat_1(B_230)
      | ~ v1_relat_1(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_768,plain,(
    ! [A_229,A_36,B_37] :
      ( r1_tarski(k1_relat_1(A_229),A_36)
      | ~ r1_tarski(A_229,k2_zfmisc_1(A_36,B_37))
      | ~ v1_relat_1(k2_zfmisc_1(A_36,B_37))
      | ~ v1_relat_1(A_229)
      | k1_xboole_0 = B_37
      | k1_xboole_0 = A_36 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_753])).

tff(c_5153,plain,(
    ! [A_482,A_483,B_484] :
      ( r1_tarski(k1_relat_1(A_482),A_483)
      | ~ r1_tarski(A_482,k2_zfmisc_1(A_483,B_484))
      | ~ v1_relat_1(A_482)
      | k1_xboole_0 = B_484
      | k1_xboole_0 = A_483 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_768])).

tff(c_5155,plain,
    ( r1_tarski(k1_relat_1('#skF_17'),k1_tarski('#skF_15'))
    | ~ v1_relat_1('#skF_17')
    | k1_xboole_0 = '#skF_16'
    | k1_tarski('#skF_15') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_293,c_5153])).

tff(c_5162,plain,
    ( r1_tarski(k1_relat_1('#skF_17'),k1_tarski('#skF_15'))
    | k1_xboole_0 = '#skF_16'
    | k1_tarski('#skF_15') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_5155])).

tff(c_5163,plain,(
    r1_tarski(k1_relat_1('#skF_17'),k1_tarski('#skF_15')) ),
    inference(negUnitSimplification,[status(thm)],[c_572,c_144,c_5162])).

tff(c_76,plain,(
    ! [B_49,A_48] :
      ( k7_relat_1(B_49,A_48) = B_49
      | ~ r1_tarski(k1_relat_1(B_49),A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5166,plain,
    ( k7_relat_1('#skF_17',k1_tarski('#skF_15')) = '#skF_17'
    | ~ v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_5163,c_76])).

tff(c_5172,plain,(
    k7_relat_1('#skF_17',k1_tarski('#skF_15')) = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_5166])).

tff(c_130,plain,(
    ! [B_140,A_139] :
      ( k2_relat_1(k7_relat_1(B_140,k1_tarski(A_139))) = k1_tarski(k1_funct_1(B_140,A_139))
      | ~ r2_hidden(A_139,k1_relat_1(B_140))
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_5186,plain,
    ( k1_tarski(k1_funct_1('#skF_17','#skF_15')) = k2_relat_1('#skF_17')
    | ~ r2_hidden('#skF_15',k1_relat_1('#skF_17'))
    | ~ v1_funct_1('#skF_17')
    | ~ v1_relat_1('#skF_17') ),
    inference(superposition,[status(thm),theory(equality)],[c_5172,c_130])).

tff(c_5216,plain,
    ( k1_tarski(k1_funct_1('#skF_17','#skF_15')) = k2_relat_1('#skF_17')
    | ~ r2_hidden('#skF_15',k1_relat_1('#skF_17')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_150,c_5186])).

tff(c_5217,plain,(
    ~ r2_hidden('#skF_15',k1_relat_1('#skF_17')) ),
    inference(negUnitSimplification,[status(thm)],[c_1009,c_5216])).

tff(c_5239,plain,
    ( k1_funct_1('#skF_17','#skF_15') = k1_xboole_0
    | ~ v1_funct_1('#skF_17')
    | ~ v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_108,c_5217])).

tff(c_5242,plain,(
    k1_funct_1('#skF_17','#skF_15') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_150,c_5239])).

tff(c_5243,plain,(
    k2_relat_1('#skF_17') != k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5242,c_1009])).

tff(c_128,plain,(
    ! [B_138,A_137] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_138,k1_tarski(A_137))),k1_tarski(k1_funct_1(B_138,A_137)))
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_5275,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1('#skF_17',k1_tarski('#skF_15'))),k1_tarski(k1_xboole_0))
    | ~ v1_funct_1('#skF_17')
    | ~ v1_relat_1('#skF_17') ),
    inference(superposition,[status(thm),theory(equality)],[c_5242,c_128])).

tff(c_5297,plain,(
    r1_tarski(k2_relat_1('#skF_17'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_150,c_5172,c_5275])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(B_17) = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_tarski(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5305,plain,
    ( k2_relat_1('#skF_17') = k1_tarski(k1_xboole_0)
    | k2_relat_1('#skF_17') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5297,c_30])).

tff(c_5308,plain,(
    k2_relat_1('#skF_17') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5243,c_5305])).

tff(c_14,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_148,plain,(
    v1_funct_2('#skF_17',k1_tarski('#skF_15'),'#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_4706,plain,(
    ! [D_457,C_458,A_459,B_460] :
      ( r2_hidden(k1_funct_1(D_457,C_458),k2_relset_1(A_459,B_460,D_457))
      | k1_xboole_0 = B_460
      | ~ r2_hidden(C_458,A_459)
      | ~ m1_subset_1(D_457,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460)))
      | ~ v1_funct_2(D_457,A_459,B_460)
      | ~ v1_funct_1(D_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_4721,plain,(
    ! [C_458] :
      ( r2_hidden(k1_funct_1('#skF_17',C_458),k2_relat_1('#skF_17'))
      | k1_xboole_0 = '#skF_16'
      | ~ r2_hidden(C_458,k1_tarski('#skF_15'))
      | ~ m1_subset_1('#skF_17',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_15'),'#skF_16')))
      | ~ v1_funct_2('#skF_17',k1_tarski('#skF_15'),'#skF_16')
      | ~ v1_funct_1('#skF_17') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_4706])).

tff(c_4723,plain,(
    ! [C_458] :
      ( r2_hidden(k1_funct_1('#skF_17',C_458),k2_relat_1('#skF_17'))
      | k1_xboole_0 = '#skF_16'
      | ~ r2_hidden(C_458,k1_tarski('#skF_15')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_148,c_146,c_4721])).

tff(c_4724,plain,(
    ! [C_458] :
      ( r2_hidden(k1_funct_1('#skF_17',C_458),k2_relat_1('#skF_17'))
      | ~ r2_hidden(C_458,k1_tarski('#skF_15')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_4723])).

tff(c_5255,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_17'))
    | ~ r2_hidden('#skF_15',k1_tarski('#skF_15')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5242,c_4724])).

tff(c_5283,plain,(
    r2_hidden(k1_xboole_0,k2_relat_1('#skF_17')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5255])).

tff(c_5310,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5308,c_5283])).

tff(c_5321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_5310])).

tff(c_5323,plain,(
    ! [A_488] : ~ r1_xboole_0(A_488,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_5327,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_5323])).

tff(c_5331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:43:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.31  
% 6.71/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.32  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_17 > #skF_6 > #skF_15 > #skF_9 > #skF_3 > #skF_16 > #skF_12 > #skF_10 > #skF_7 > #skF_2 > #skF_8 > #skF_14 > #skF_1 > #skF_5 > #skF_4
% 6.71/2.32  
% 6.71/2.32  %Foreground sorts:
% 6.71/2.32  
% 6.71/2.32  
% 6.71/2.32  %Background operators:
% 6.71/2.32  
% 6.71/2.32  
% 6.71/2.32  %Foreground operators:
% 6.71/2.32  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 6.71/2.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.71/2.32  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 6.71/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.71/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.71/2.32  tff('#skF_17', type, '#skF_17': $i).
% 6.71/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.71/2.32  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.71/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.71/2.32  tff('#skF_15', type, '#skF_15': $i).
% 6.71/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.71/2.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.71/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.71/2.32  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 6.71/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.71/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.71/2.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.71/2.32  tff('#skF_16', type, '#skF_16': $i).
% 6.71/2.32  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 6.71/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.71/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.71/2.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.71/2.32  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 6.71/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.71/2.32  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.71/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.71/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.71/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.71/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.71/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.71/2.32  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 6.71/2.32  tff('#skF_14', type, '#skF_14': ($i * $i * $i * $i) > $i).
% 6.71/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.71/2.32  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.71/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.71/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.71/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.71/2.32  
% 6.71/2.34  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.71/2.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.71/2.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.71/2.34  tff(f_265, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 6.71/2.34  tff(f_222, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.71/2.34  tff(f_189, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 6.71/2.34  tff(f_226, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.71/2.34  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.71/2.34  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.71/2.34  tff(f_140, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.71/2.34  tff(f_84, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 6.71/2.34  tff(f_144, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 6.71/2.34  tff(f_68, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 6.71/2.34  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.71/2.34  tff(f_117, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 6.71/2.34  tff(f_137, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.71/2.34  tff(f_154, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 6.71/2.34  tff(f_218, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 6.71/2.34  tff(f_210, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 6.71/2.34  tff(f_64, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 6.71/2.34  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.71/2.34  tff(f_253, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 6.71/2.34  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.71/2.34  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.71/2.34  tff(c_294, plain, (![A_183, B_184, C_185]: (~r1_xboole_0(A_183, B_184) | ~r2_hidden(C_185, k3_xboole_0(A_183, B_184)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.71/2.34  tff(c_297, plain, (![A_8, C_185]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_185, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_294])).
% 6.71/2.34  tff(c_298, plain, (![C_185]: (~r2_hidden(C_185, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_297])).
% 6.71/2.34  tff(c_146, plain, (m1_subset_1('#skF_17', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_15'), '#skF_16')))), inference(cnfTransformation, [status(thm)], [f_265])).
% 6.71/2.34  tff(c_311, plain, (![C_189, A_190, B_191]: (v1_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_222])).
% 6.71/2.34  tff(c_324, plain, (v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_146, c_311])).
% 6.71/2.34  tff(c_150, plain, (v1_funct_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_265])).
% 6.71/2.34  tff(c_108, plain, (![A_92, B_95]: (k1_funct_1(A_92, B_95)=k1_xboole_0 | r2_hidden(B_95, k1_relat_1(A_92)) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.71/2.34  tff(c_980, plain, (![A_247, B_248, C_249]: (k2_relset_1(A_247, B_248, C_249)=k2_relat_1(C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.71/2.34  tff(c_995, plain, (k2_relset_1(k1_tarski('#skF_15'), '#skF_16', '#skF_17')=k2_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_146, c_980])).
% 6.71/2.34  tff(c_142, plain, (k2_relset_1(k1_tarski('#skF_15'), '#skF_16', '#skF_17')!=k1_tarski(k1_funct_1('#skF_17', '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 6.71/2.34  tff(c_1009, plain, (k1_tarski(k1_funct_1('#skF_17', '#skF_15'))!=k2_relat_1('#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_995, c_142])).
% 6.71/2.34  tff(c_28, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.71/2.34  tff(c_190, plain, (![A_161, B_162]: (v1_relat_1(k2_zfmisc_1(A_161, B_162)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.71/2.34  tff(c_192, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_190])).
% 6.71/2.34  tff(c_70, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.71/2.34  tff(c_48, plain, (![A_27]: (k7_relat_1(k1_xboole_0, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.71/2.34  tff(c_519, plain, (![B_212, A_213]: (k3_xboole_0(k1_relat_1(B_212), A_213)=k1_relat_1(k7_relat_1(B_212, A_213)) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.71/2.34  tff(c_546, plain, (![A_213]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_213))=k3_xboole_0(k1_xboole_0, A_213) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_519])).
% 6.71/2.34  tff(c_553, plain, (![A_214]: (k3_xboole_0(k1_xboole_0, A_214)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_70, c_48, c_546])).
% 6.71/2.34  tff(c_36, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | k3_xboole_0(A_18, k1_tarski(B_19))!=k1_tarski(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.71/2.34  tff(c_559, plain, (![B_19]: (r2_hidden(B_19, k1_xboole_0) | k1_tarski(B_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_553, c_36])).
% 6.71/2.34  tff(c_572, plain, (![B_19]: (k1_tarski(B_19)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_298, c_559])).
% 6.71/2.34  tff(c_144, plain, (k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_265])).
% 6.71/2.34  tff(c_285, plain, (![A_181, B_182]: (r1_tarski(A_181, B_182) | ~m1_subset_1(A_181, k1_zfmisc_1(B_182)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.71/2.34  tff(c_293, plain, (r1_tarski('#skF_17', k2_zfmisc_1(k1_tarski('#skF_15'), '#skF_16'))), inference(resolution, [status(thm)], [c_146, c_285])).
% 6.71/2.34  tff(c_44, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.71/2.34  tff(c_60, plain, (![A_36, B_37]: (k1_relat_1(k2_zfmisc_1(A_36, B_37))=A_36 | k1_xboole_0=B_37 | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.71/2.34  tff(c_753, plain, (![A_229, B_230]: (r1_tarski(k1_relat_1(A_229), k1_relat_1(B_230)) | ~r1_tarski(A_229, B_230) | ~v1_relat_1(B_230) | ~v1_relat_1(A_229))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.71/2.34  tff(c_768, plain, (![A_229, A_36, B_37]: (r1_tarski(k1_relat_1(A_229), A_36) | ~r1_tarski(A_229, k2_zfmisc_1(A_36, B_37)) | ~v1_relat_1(k2_zfmisc_1(A_36, B_37)) | ~v1_relat_1(A_229) | k1_xboole_0=B_37 | k1_xboole_0=A_36)), inference(superposition, [status(thm), theory('equality')], [c_60, c_753])).
% 6.71/2.34  tff(c_5153, plain, (![A_482, A_483, B_484]: (r1_tarski(k1_relat_1(A_482), A_483) | ~r1_tarski(A_482, k2_zfmisc_1(A_483, B_484)) | ~v1_relat_1(A_482) | k1_xboole_0=B_484 | k1_xboole_0=A_483)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_768])).
% 6.71/2.34  tff(c_5155, plain, (r1_tarski(k1_relat_1('#skF_17'), k1_tarski('#skF_15')) | ~v1_relat_1('#skF_17') | k1_xboole_0='#skF_16' | k1_tarski('#skF_15')=k1_xboole_0), inference(resolution, [status(thm)], [c_293, c_5153])).
% 6.71/2.34  tff(c_5162, plain, (r1_tarski(k1_relat_1('#skF_17'), k1_tarski('#skF_15')) | k1_xboole_0='#skF_16' | k1_tarski('#skF_15')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_324, c_5155])).
% 6.71/2.34  tff(c_5163, plain, (r1_tarski(k1_relat_1('#skF_17'), k1_tarski('#skF_15'))), inference(negUnitSimplification, [status(thm)], [c_572, c_144, c_5162])).
% 6.71/2.34  tff(c_76, plain, (![B_49, A_48]: (k7_relat_1(B_49, A_48)=B_49 | ~r1_tarski(k1_relat_1(B_49), A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.71/2.34  tff(c_5166, plain, (k7_relat_1('#skF_17', k1_tarski('#skF_15'))='#skF_17' | ~v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_5163, c_76])).
% 6.71/2.34  tff(c_5172, plain, (k7_relat_1('#skF_17', k1_tarski('#skF_15'))='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_5166])).
% 6.71/2.34  tff(c_130, plain, (![B_140, A_139]: (k2_relat_1(k7_relat_1(B_140, k1_tarski(A_139)))=k1_tarski(k1_funct_1(B_140, A_139)) | ~r2_hidden(A_139, k1_relat_1(B_140)) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_218])).
% 6.71/2.34  tff(c_5186, plain, (k1_tarski(k1_funct_1('#skF_17', '#skF_15'))=k2_relat_1('#skF_17') | ~r2_hidden('#skF_15', k1_relat_1('#skF_17')) | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_5172, c_130])).
% 6.71/2.34  tff(c_5216, plain, (k1_tarski(k1_funct_1('#skF_17', '#skF_15'))=k2_relat_1('#skF_17') | ~r2_hidden('#skF_15', k1_relat_1('#skF_17'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_150, c_5186])).
% 6.71/2.34  tff(c_5217, plain, (~r2_hidden('#skF_15', k1_relat_1('#skF_17'))), inference(negUnitSimplification, [status(thm)], [c_1009, c_5216])).
% 6.71/2.34  tff(c_5239, plain, (k1_funct_1('#skF_17', '#skF_15')=k1_xboole_0 | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_108, c_5217])).
% 6.71/2.34  tff(c_5242, plain, (k1_funct_1('#skF_17', '#skF_15')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_324, c_150, c_5239])).
% 6.71/2.34  tff(c_5243, plain, (k2_relat_1('#skF_17')!=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5242, c_1009])).
% 6.71/2.34  tff(c_128, plain, (![B_138, A_137]: (r1_tarski(k2_relat_1(k7_relat_1(B_138, k1_tarski(A_137))), k1_tarski(k1_funct_1(B_138, A_137))) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.34  tff(c_5275, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_17', k1_tarski('#skF_15'))), k1_tarski(k1_xboole_0)) | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_5242, c_128])).
% 6.71/2.34  tff(c_5297, plain, (r1_tarski(k2_relat_1('#skF_17'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_150, c_5172, c_5275])).
% 6.71/2.34  tff(c_30, plain, (![B_17, A_16]: (k1_tarski(B_17)=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.71/2.34  tff(c_5305, plain, (k2_relat_1('#skF_17')=k1_tarski(k1_xboole_0) | k2_relat_1('#skF_17')=k1_xboole_0), inference(resolution, [status(thm)], [c_5297, c_30])).
% 6.71/2.34  tff(c_5308, plain, (k2_relat_1('#skF_17')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5243, c_5305])).
% 6.71/2.34  tff(c_14, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.71/2.34  tff(c_148, plain, (v1_funct_2('#skF_17', k1_tarski('#skF_15'), '#skF_16')), inference(cnfTransformation, [status(thm)], [f_265])).
% 6.71/2.34  tff(c_4706, plain, (![D_457, C_458, A_459, B_460]: (r2_hidden(k1_funct_1(D_457, C_458), k2_relset_1(A_459, B_460, D_457)) | k1_xboole_0=B_460 | ~r2_hidden(C_458, A_459) | ~m1_subset_1(D_457, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))) | ~v1_funct_2(D_457, A_459, B_460) | ~v1_funct_1(D_457))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.71/2.34  tff(c_4721, plain, (![C_458]: (r2_hidden(k1_funct_1('#skF_17', C_458), k2_relat_1('#skF_17')) | k1_xboole_0='#skF_16' | ~r2_hidden(C_458, k1_tarski('#skF_15')) | ~m1_subset_1('#skF_17', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_15'), '#skF_16'))) | ~v1_funct_2('#skF_17', k1_tarski('#skF_15'), '#skF_16') | ~v1_funct_1('#skF_17'))), inference(superposition, [status(thm), theory('equality')], [c_995, c_4706])).
% 6.71/2.34  tff(c_4723, plain, (![C_458]: (r2_hidden(k1_funct_1('#skF_17', C_458), k2_relat_1('#skF_17')) | k1_xboole_0='#skF_16' | ~r2_hidden(C_458, k1_tarski('#skF_15')))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_148, c_146, c_4721])).
% 6.71/2.34  tff(c_4724, plain, (![C_458]: (r2_hidden(k1_funct_1('#skF_17', C_458), k2_relat_1('#skF_17')) | ~r2_hidden(C_458, k1_tarski('#skF_15')))), inference(negUnitSimplification, [status(thm)], [c_144, c_4723])).
% 6.71/2.34  tff(c_5255, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_17')) | ~r2_hidden('#skF_15', k1_tarski('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_5242, c_4724])).
% 6.71/2.34  tff(c_5283, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_17'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5255])).
% 6.71/2.34  tff(c_5310, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5308, c_5283])).
% 6.71/2.34  tff(c_5321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_5310])).
% 6.71/2.34  tff(c_5323, plain, (![A_488]: (~r1_xboole_0(A_488, k1_xboole_0))), inference(splitRight, [status(thm)], [c_297])).
% 6.71/2.34  tff(c_5327, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_5323])).
% 6.71/2.34  tff(c_5331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_5327])).
% 6.71/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.34  
% 6.71/2.34  Inference rules
% 6.71/2.34  ----------------------
% 6.71/2.34  #Ref     : 0
% 6.71/2.34  #Sup     : 1140
% 6.71/2.34  #Fact    : 0
% 6.71/2.34  #Define  : 0
% 6.71/2.34  #Split   : 5
% 6.71/2.34  #Chain   : 0
% 6.71/2.34  #Close   : 0
% 6.71/2.34  
% 6.71/2.34  Ordering : KBO
% 6.71/2.34  
% 6.71/2.34  Simplification rules
% 6.71/2.34  ----------------------
% 6.71/2.34  #Subsume      : 312
% 6.71/2.34  #Demod        : 713
% 6.71/2.34  #Tautology    : 286
% 6.71/2.34  #SimpNegUnit  : 76
% 6.71/2.34  #BackRed      : 12
% 6.71/2.34  
% 6.71/2.34  #Partial instantiations: 0
% 6.71/2.34  #Strategies tried      : 1
% 6.71/2.34  
% 6.71/2.34  Timing (in seconds)
% 6.71/2.34  ----------------------
% 6.71/2.34  Preprocessing        : 0.42
% 6.71/2.34  Parsing              : 0.21
% 6.71/2.34  CNF conversion       : 0.04
% 6.71/2.34  Main loop            : 1.16
% 6.71/2.34  Inferencing          : 0.39
% 6.71/2.34  Reduction            : 0.38
% 6.71/2.34  Demodulation         : 0.28
% 6.71/2.34  BG Simplification    : 0.06
% 6.71/2.34  Subsumption          : 0.25
% 6.71/2.34  Abstraction          : 0.07
% 6.71/2.34  MUC search           : 0.00
% 6.71/2.34  Cooper               : 0.00
% 6.71/2.34  Total                : 1.63
% 6.71/2.34  Index Insertion      : 0.00
% 6.71/2.34  Index Deletion       : 0.00
% 6.71/2.34  Index Matching       : 0.00
% 6.71/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
