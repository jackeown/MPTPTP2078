%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:17 EST 2020

% Result     : Theorem 21.81s
% Output     : CNFRefutation 21.95s
% Verified   : 
% Statistics : Number of formulae       :  142 (1298 expanded)
%              Number of leaves         :   43 ( 444 expanded)
%              Depth                    :   13
%              Number of atoms          :  254 (3359 expanded)
%              Number of equality atoms :   79 ( 594 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1601,plain,(
    ! [A_217,B_218,C_219,D_220] :
      ( r2_relset_1(A_217,B_218,C_219,C_219)
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1655,plain,(
    ! [C_224] :
      ( r2_relset_1('#skF_5','#skF_6',C_224,C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_66,c_1601])).

tff(c_1675,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_1655])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_143,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_164,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_143])).

tff(c_76,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_74,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_912,plain,(
    ! [A_169,B_170,C_171] :
      ( k1_relset_1(A_169,B_170,C_171) = k1_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_945,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_912])).

tff(c_1183,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1201,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_1183])).

tff(c_1220,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_945,c_1201])).

tff(c_1312,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1220])).

tff(c_163,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_143])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_944,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_912])).

tff(c_1198,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1183])).

tff(c_1217,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_944,c_1198])).

tff(c_1270,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1217])).

tff(c_166,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_188,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_166])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1290,plain,(
    ! [A_20] :
      ( r1_tarski('#skF_5',A_20)
      | ~ v4_relat_1('#skF_8',A_20)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_34])).

tff(c_1405,plain,(
    ! [A_202] :
      ( r1_tarski('#skF_5',A_202)
      | ~ v4_relat_1('#skF_8',A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1290])).

tff(c_1414,plain,(
    r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_188,c_1405])).

tff(c_1704,plain,(
    ! [A_226,B_227] :
      ( r2_hidden('#skF_4'(A_226,B_227),k1_relat_1(A_226))
      | B_227 = A_226
      | k1_relat_1(B_227) != k1_relat_1(A_226)
      | ~ v1_funct_1(B_227)
      | ~ v1_relat_1(B_227)
      | ~ v1_funct_1(A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1717,plain,(
    ! [B_227] :
      ( r2_hidden('#skF_4'('#skF_8',B_227),'#skF_5')
      | B_227 = '#skF_8'
      | k1_relat_1(B_227) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_227)
      | ~ v1_relat_1(B_227)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_1704])).

tff(c_7288,plain,(
    ! [B_471] :
      ( r2_hidden('#skF_4'('#skF_8',B_471),'#skF_5')
      | B_471 = '#skF_8'
      | k1_relat_1(B_471) != '#skF_5'
      | ~ v1_funct_1(B_471)
      | ~ v1_relat_1(B_471) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_70,c_1270,c_1717])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_295,plain,(
    ! [A_91,C_92,B_93] :
      ( m1_subset_1(A_91,C_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(C_92))
      | ~ r2_hidden(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_304,plain,(
    ! [A_91,B_16,A_15] :
      ( m1_subset_1(A_91,B_16)
      | ~ r2_hidden(A_91,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_28,c_295])).

tff(c_47930,plain,(
    ! [B_1760,B_1761] :
      ( m1_subset_1('#skF_4'('#skF_8',B_1760),B_1761)
      | ~ r1_tarski('#skF_5',B_1761)
      | B_1760 = '#skF_8'
      | k1_relat_1(B_1760) != '#skF_5'
      | ~ v1_funct_1(B_1760)
      | ~ v1_relat_1(B_1760) ) ),
    inference(resolution,[status(thm)],[c_7288,c_304])).

tff(c_64,plain,(
    ! [E_48] :
      ( k1_funct_1('#skF_7',E_48) = k1_funct_1('#skF_8',E_48)
      | ~ m1_subset_1(E_48,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48236,plain,(
    ! [B_1760] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_8',B_1760)) = k1_funct_1('#skF_8','#skF_4'('#skF_8',B_1760))
      | ~ r1_tarski('#skF_5','#skF_5')
      | B_1760 = '#skF_8'
      | k1_relat_1(B_1760) != '#skF_5'
      | ~ v1_funct_1(B_1760)
      | ~ v1_relat_1(B_1760) ) ),
    inference(resolution,[status(thm)],[c_47930,c_64])).

tff(c_48339,plain,(
    ! [B_1762] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_8',B_1762)) = k1_funct_1('#skF_8','#skF_4'('#skF_8',B_1762))
      | B_1762 = '#skF_8'
      | k1_relat_1(B_1762) != '#skF_5'
      | ~ v1_funct_1(B_1762)
      | ~ v1_relat_1(B_1762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_48236])).

tff(c_36,plain,(
    ! [B_26,A_22] :
      ( k1_funct_1(B_26,'#skF_4'(A_22,B_26)) != k1_funct_1(A_22,'#skF_4'(A_22,B_26))
      | B_26 = A_22
      | k1_relat_1(B_26) != k1_relat_1(A_22)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48346,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_48339,c_36])).

tff(c_48353,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_1312,c_163,c_70,c_1270,c_1312,c_48346])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48481,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48353,c_62])).

tff(c_48494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_48481])).

tff(c_48495,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1220])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48540,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48495,c_6])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48538,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48495,c_48495,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_404,plain,(
    ! [C_113,A_114,B_115] :
      ( r2_hidden(C_113,A_114)
      | ~ r2_hidden(C_113,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_463,plain,(
    ! [A_119,A_120] :
      ( r2_hidden('#skF_1'(A_119),A_120)
      | ~ m1_subset_1(A_119,k1_zfmisc_1(A_120))
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_4,c_404])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_487,plain,(
    ! [A_122,A_123] :
      ( ~ v1_xboole_0(A_122)
      | ~ m1_subset_1(A_123,k1_zfmisc_1(A_122))
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_463,c_2])).

tff(c_506,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_487])).

tff(c_510,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_48619,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48538,c_510])).

tff(c_48628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48540,c_48619])).

tff(c_48629,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_48673,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48629,c_6])).

tff(c_48671,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48629,c_48629,c_18])).

tff(c_48759,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48671,c_510])).

tff(c_48768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48673,c_48759])).

tff(c_48769,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_48776,plain,(
    ! [A_1775,B_1776] :
      ( r2_hidden('#skF_2'(A_1775,B_1776),B_1776)
      | r2_hidden('#skF_3'(A_1775,B_1776),A_1775)
      | B_1776 = A_1775 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48827,plain,(
    ! [B_1781,A_1782] :
      ( ~ v1_xboole_0(B_1781)
      | r2_hidden('#skF_3'(A_1782,B_1781),A_1782)
      | B_1781 = A_1782 ) ),
    inference(resolution,[status(thm)],[c_48776,c_2])).

tff(c_48842,plain,(
    ! [A_1783,B_1784] :
      ( ~ v1_xboole_0(A_1783)
      | ~ v1_xboole_0(B_1784)
      | B_1784 = A_1783 ) ),
    inference(resolution,[status(thm)],[c_48827,c_2])).

tff(c_48855,plain,(
    ! [B_1785] :
      ( ~ v1_xboole_0(B_1785)
      | k1_xboole_0 = B_1785 ) ),
    inference(resolution,[status(thm)],[c_6,c_48842])).

tff(c_48870,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_48769,c_48855])).

tff(c_48770,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_507,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_487])).

tff(c_48771,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_48773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48770,c_48771])).

tff(c_48774,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_48869,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_48774,c_48855])).

tff(c_48899,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48870,c_48869])).

tff(c_24,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48891,plain,(
    ! [A_14] : m1_subset_1('#skF_7',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48869,c_24])).

tff(c_49080,plain,(
    ! [A_14] : m1_subset_1('#skF_8',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48899,c_48891])).

tff(c_50913,plain,(
    ! [A_1973,B_1974,C_1975,D_1976] :
      ( r2_relset_1(A_1973,B_1974,C_1975,C_1975)
      | ~ m1_subset_1(D_1976,k1_zfmisc_1(k2_zfmisc_1(A_1973,B_1974)))
      | ~ m1_subset_1(C_1975,k1_zfmisc_1(k2_zfmisc_1(A_1973,B_1974))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_51908,plain,(
    ! [A_2072,B_2073,C_2074] :
      ( r2_relset_1(A_2072,B_2073,C_2074,C_2074)
      | ~ m1_subset_1(C_2074,k1_zfmisc_1(k2_zfmisc_1(A_2072,B_2073))) ) ),
    inference(resolution,[status(thm)],[c_49080,c_50913])).

tff(c_51930,plain,(
    ! [A_2072,B_2073] : r2_relset_1(A_2072,B_2073,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_49080,c_51908])).

tff(c_49875,plain,(
    ! [A_1871,B_1872,C_1873,D_1874] :
      ( r2_relset_1(A_1871,B_1872,C_1873,C_1873)
      | ~ m1_subset_1(D_1874,k1_zfmisc_1(k2_zfmisc_1(A_1871,B_1872)))
      | ~ m1_subset_1(C_1873,k1_zfmisc_1(k2_zfmisc_1(A_1871,B_1872))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50868,plain,(
    ! [A_1970,B_1971,C_1972] :
      ( r2_relset_1(A_1970,B_1971,C_1972,C_1972)
      | ~ m1_subset_1(C_1972,k1_zfmisc_1(k2_zfmisc_1(A_1970,B_1971))) ) ),
    inference(resolution,[status(thm)],[c_49080,c_49875])).

tff(c_50890,plain,(
    ! [A_1970,B_1971] : r2_relset_1(A_1970,B_1971,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_49080,c_50868])).

tff(c_48775,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_48868,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48775,c_48855])).

tff(c_49041,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48870,c_48868])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48886,plain,(
    ! [B_9,A_8] :
      ( B_9 = '#skF_7'
      | A_8 = '#skF_7'
      | k2_zfmisc_1(A_8,B_9) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48869,c_48869,c_48869,c_16])).

tff(c_49850,plain,(
    ! [B_1869,A_1870] :
      ( B_1869 = '#skF_8'
      | A_1870 = '#skF_8'
      | k2_zfmisc_1(A_1870,B_1869) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48899,c_48899,c_48899,c_48886])).

tff(c_49860,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_49041,c_49850])).

tff(c_49865,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_49860])).

tff(c_48915,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48899,c_62])).

tff(c_49867,plain,(
    ~ r2_relset_1('#skF_8','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49865,c_48915])).

tff(c_50895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50890,c_49867])).

tff(c_50896,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_49860])).

tff(c_50899,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50896,c_48915])).

tff(c_51935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51930,c_50899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:42:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.81/12.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.81/12.93  
% 21.81/12.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.81/12.93  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 21.81/12.93  
% 21.81/12.93  %Foreground sorts:
% 21.81/12.93  
% 21.81/12.93  
% 21.81/12.93  %Background operators:
% 21.81/12.93  
% 21.81/12.93  
% 21.81/12.93  %Foreground operators:
% 21.81/12.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.81/12.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.81/12.93  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 21.81/12.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.81/12.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 21.81/12.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.81/12.93  tff('#skF_7', type, '#skF_7': $i).
% 21.81/12.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 21.81/12.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.81/12.93  tff('#skF_5', type, '#skF_5': $i).
% 21.81/12.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.81/12.93  tff('#skF_6', type, '#skF_6': $i).
% 21.81/12.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 21.81/12.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.81/12.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.81/12.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 21.81/12.93  tff('#skF_8', type, '#skF_8': $i).
% 21.81/12.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.81/12.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.81/12.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.81/12.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.81/12.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 21.81/12.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.81/12.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.81/12.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.81/12.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 21.81/12.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.81/12.93  
% 21.95/12.95  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 21.95/12.95  tff(f_108, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 21.95/12.95  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 21.95/12.95  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 21.95/12.95  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 21.95/12.95  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 21.95/12.95  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 21.95/12.95  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 21.95/12.95  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.95/12.95  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 21.95/12.95  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 21.95/12.95  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 21.95/12.95  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 21.95/12.95  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 21.95/12.95  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 21.95/12.95  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 21.95/12.95  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_1601, plain, (![A_217, B_218, C_219, D_220]: (r2_relset_1(A_217, B_218, C_219, C_219) | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.95/12.95  tff(c_1655, plain, (![C_224]: (r2_relset_1('#skF_5', '#skF_6', C_224, C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_66, c_1601])).
% 21.95/12.95  tff(c_1675, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_66, c_1655])).
% 21.95/12.95  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_143, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 21.95/12.95  tff(c_164, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_143])).
% 21.95/12.95  tff(c_76, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_74, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_912, plain, (![A_169, B_170, C_171]: (k1_relset_1(A_169, B_170, C_171)=k1_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 21.95/12.95  tff(c_945, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_912])).
% 21.95/12.95  tff(c_1183, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 21.95/12.95  tff(c_1201, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_1183])).
% 21.95/12.95  tff(c_1220, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_945, c_1201])).
% 21.95/12.95  tff(c_1312, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1220])).
% 21.95/12.95  tff(c_163, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_143])).
% 21.95/12.95  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_68, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_944, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_912])).
% 21.95/12.95  tff(c_1198, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_1183])).
% 21.95/12.95  tff(c_1217, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_944, c_1198])).
% 21.95/12.95  tff(c_1270, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1217])).
% 21.95/12.95  tff(c_166, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 21.95/12.95  tff(c_188, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_166])).
% 21.95/12.95  tff(c_34, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(B_21), A_20) | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.95/12.95  tff(c_1290, plain, (![A_20]: (r1_tarski('#skF_5', A_20) | ~v4_relat_1('#skF_8', A_20) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1270, c_34])).
% 21.95/12.95  tff(c_1405, plain, (![A_202]: (r1_tarski('#skF_5', A_202) | ~v4_relat_1('#skF_8', A_202))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1290])).
% 21.95/12.95  tff(c_1414, plain, (r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_188, c_1405])).
% 21.95/12.95  tff(c_1704, plain, (![A_226, B_227]: (r2_hidden('#skF_4'(A_226, B_227), k1_relat_1(A_226)) | B_227=A_226 | k1_relat_1(B_227)!=k1_relat_1(A_226) | ~v1_funct_1(B_227) | ~v1_relat_1(B_227) | ~v1_funct_1(A_226) | ~v1_relat_1(A_226))), inference(cnfTransformation, [status(thm)], [f_88])).
% 21.95/12.95  tff(c_1717, plain, (![B_227]: (r2_hidden('#skF_4'('#skF_8', B_227), '#skF_5') | B_227='#skF_8' | k1_relat_1(B_227)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_227) | ~v1_relat_1(B_227) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1270, c_1704])).
% 21.95/12.95  tff(c_7288, plain, (![B_471]: (r2_hidden('#skF_4'('#skF_8', B_471), '#skF_5') | B_471='#skF_8' | k1_relat_1(B_471)!='#skF_5' | ~v1_funct_1(B_471) | ~v1_relat_1(B_471))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_70, c_1270, c_1717])).
% 21.95/12.95  tff(c_28, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.95/12.95  tff(c_295, plain, (![A_91, C_92, B_93]: (m1_subset_1(A_91, C_92) | ~m1_subset_1(B_93, k1_zfmisc_1(C_92)) | ~r2_hidden(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 21.95/12.95  tff(c_304, plain, (![A_91, B_16, A_15]: (m1_subset_1(A_91, B_16) | ~r2_hidden(A_91, A_15) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_28, c_295])).
% 21.95/12.95  tff(c_47930, plain, (![B_1760, B_1761]: (m1_subset_1('#skF_4'('#skF_8', B_1760), B_1761) | ~r1_tarski('#skF_5', B_1761) | B_1760='#skF_8' | k1_relat_1(B_1760)!='#skF_5' | ~v1_funct_1(B_1760) | ~v1_relat_1(B_1760))), inference(resolution, [status(thm)], [c_7288, c_304])).
% 21.95/12.95  tff(c_64, plain, (![E_48]: (k1_funct_1('#skF_7', E_48)=k1_funct_1('#skF_8', E_48) | ~m1_subset_1(E_48, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_48236, plain, (![B_1760]: (k1_funct_1('#skF_7', '#skF_4'('#skF_8', B_1760))=k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_1760)) | ~r1_tarski('#skF_5', '#skF_5') | B_1760='#skF_8' | k1_relat_1(B_1760)!='#skF_5' | ~v1_funct_1(B_1760) | ~v1_relat_1(B_1760))), inference(resolution, [status(thm)], [c_47930, c_64])).
% 21.95/12.95  tff(c_48339, plain, (![B_1762]: (k1_funct_1('#skF_7', '#skF_4'('#skF_8', B_1762))=k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_1762)) | B_1762='#skF_8' | k1_relat_1(B_1762)!='#skF_5' | ~v1_funct_1(B_1762) | ~v1_relat_1(B_1762))), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_48236])).
% 21.95/12.95  tff(c_36, plain, (![B_26, A_22]: (k1_funct_1(B_26, '#skF_4'(A_22, B_26))!=k1_funct_1(A_22, '#skF_4'(A_22, B_26)) | B_26=A_22 | k1_relat_1(B_26)!=k1_relat_1(A_22) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 21.95/12.95  tff(c_48346, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_48339, c_36])).
% 21.95/12.95  tff(c_48353, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_1312, c_163, c_70, c_1270, c_1312, c_48346])).
% 21.95/12.95  tff(c_62, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_147])).
% 21.95/12.95  tff(c_48481, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48353, c_62])).
% 21.95/12.95  tff(c_48494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1675, c_48481])).
% 21.95/12.95  tff(c_48495, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1220])).
% 21.95/12.95  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.95/12.95  tff(c_48540, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48495, c_6])).
% 21.95/12.95  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.95/12.95  tff(c_48538, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48495, c_48495, c_18])).
% 21.95/12.95  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.95/12.95  tff(c_404, plain, (![C_113, A_114, B_115]: (r2_hidden(C_113, A_114) | ~r2_hidden(C_113, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.95/12.95  tff(c_463, plain, (![A_119, A_120]: (r2_hidden('#skF_1'(A_119), A_120) | ~m1_subset_1(A_119, k1_zfmisc_1(A_120)) | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_4, c_404])).
% 21.95/12.95  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.95/12.95  tff(c_487, plain, (![A_122, A_123]: (~v1_xboole_0(A_122) | ~m1_subset_1(A_123, k1_zfmisc_1(A_122)) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_463, c_2])).
% 21.95/12.95  tff(c_506, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_66, c_487])).
% 21.95/12.95  tff(c_510, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_506])).
% 21.95/12.95  tff(c_48619, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48538, c_510])).
% 21.95/12.95  tff(c_48628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48540, c_48619])).
% 21.95/12.95  tff(c_48629, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1217])).
% 21.95/12.95  tff(c_48673, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48629, c_6])).
% 21.95/12.95  tff(c_48671, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48629, c_48629, c_18])).
% 21.95/12.95  tff(c_48759, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48671, c_510])).
% 21.95/12.95  tff(c_48768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48673, c_48759])).
% 21.95/12.95  tff(c_48769, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_506])).
% 21.95/12.95  tff(c_48776, plain, (![A_1775, B_1776]: (r2_hidden('#skF_2'(A_1775, B_1776), B_1776) | r2_hidden('#skF_3'(A_1775, B_1776), A_1775) | B_1776=A_1775)), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.95/12.95  tff(c_48827, plain, (![B_1781, A_1782]: (~v1_xboole_0(B_1781) | r2_hidden('#skF_3'(A_1782, B_1781), A_1782) | B_1781=A_1782)), inference(resolution, [status(thm)], [c_48776, c_2])).
% 21.95/12.95  tff(c_48842, plain, (![A_1783, B_1784]: (~v1_xboole_0(A_1783) | ~v1_xboole_0(B_1784) | B_1784=A_1783)), inference(resolution, [status(thm)], [c_48827, c_2])).
% 21.95/12.95  tff(c_48855, plain, (![B_1785]: (~v1_xboole_0(B_1785) | k1_xboole_0=B_1785)), inference(resolution, [status(thm)], [c_6, c_48842])).
% 21.95/12.95  tff(c_48870, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_48769, c_48855])).
% 21.95/12.95  tff(c_48770, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_506])).
% 21.95/12.95  tff(c_507, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_72, c_487])).
% 21.95/12.95  tff(c_48771, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_507])).
% 21.95/12.95  tff(c_48773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48770, c_48771])).
% 21.95/12.95  tff(c_48774, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_507])).
% 21.95/12.95  tff(c_48869, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_48774, c_48855])).
% 21.95/12.95  tff(c_48899, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48870, c_48869])).
% 21.95/12.95  tff(c_24, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.95/12.95  tff(c_48891, plain, (![A_14]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_48869, c_24])).
% 21.95/12.95  tff(c_49080, plain, (![A_14]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_48899, c_48891])).
% 21.95/12.95  tff(c_50913, plain, (![A_1973, B_1974, C_1975, D_1976]: (r2_relset_1(A_1973, B_1974, C_1975, C_1975) | ~m1_subset_1(D_1976, k1_zfmisc_1(k2_zfmisc_1(A_1973, B_1974))) | ~m1_subset_1(C_1975, k1_zfmisc_1(k2_zfmisc_1(A_1973, B_1974))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.95/12.95  tff(c_51908, plain, (![A_2072, B_2073, C_2074]: (r2_relset_1(A_2072, B_2073, C_2074, C_2074) | ~m1_subset_1(C_2074, k1_zfmisc_1(k2_zfmisc_1(A_2072, B_2073))))), inference(resolution, [status(thm)], [c_49080, c_50913])).
% 21.95/12.95  tff(c_51930, plain, (![A_2072, B_2073]: (r2_relset_1(A_2072, B_2073, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_49080, c_51908])).
% 21.95/12.95  tff(c_49875, plain, (![A_1871, B_1872, C_1873, D_1874]: (r2_relset_1(A_1871, B_1872, C_1873, C_1873) | ~m1_subset_1(D_1874, k1_zfmisc_1(k2_zfmisc_1(A_1871, B_1872))) | ~m1_subset_1(C_1873, k1_zfmisc_1(k2_zfmisc_1(A_1871, B_1872))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.95/12.95  tff(c_50868, plain, (![A_1970, B_1971, C_1972]: (r2_relset_1(A_1970, B_1971, C_1972, C_1972) | ~m1_subset_1(C_1972, k1_zfmisc_1(k2_zfmisc_1(A_1970, B_1971))))), inference(resolution, [status(thm)], [c_49080, c_49875])).
% 21.95/12.95  tff(c_50890, plain, (![A_1970, B_1971]: (r2_relset_1(A_1970, B_1971, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_49080, c_50868])).
% 21.95/12.95  tff(c_48775, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_507])).
% 21.95/12.95  tff(c_48868, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_48775, c_48855])).
% 21.95/12.95  tff(c_49041, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48870, c_48868])).
% 21.95/12.95  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.95/12.95  tff(c_48886, plain, (![B_9, A_8]: (B_9='#skF_7' | A_8='#skF_7' | k2_zfmisc_1(A_8, B_9)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48869, c_48869, c_48869, c_16])).
% 21.95/12.95  tff(c_49850, plain, (![B_1869, A_1870]: (B_1869='#skF_8' | A_1870='#skF_8' | k2_zfmisc_1(A_1870, B_1869)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48899, c_48899, c_48899, c_48886])).
% 21.95/12.95  tff(c_49860, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_49041, c_49850])).
% 21.95/12.95  tff(c_49865, plain, ('#skF_5'='#skF_8'), inference(splitLeft, [status(thm)], [c_49860])).
% 21.95/12.95  tff(c_48915, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48899, c_62])).
% 21.95/12.95  tff(c_49867, plain, (~r2_relset_1('#skF_8', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_49865, c_48915])).
% 21.95/12.95  tff(c_50895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50890, c_49867])).
% 21.95/12.95  tff(c_50896, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_49860])).
% 21.95/12.95  tff(c_50899, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50896, c_48915])).
% 21.95/12.95  tff(c_51935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51930, c_50899])).
% 21.95/12.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.95/12.95  
% 21.95/12.95  Inference rules
% 21.95/12.95  ----------------------
% 21.95/12.95  #Ref     : 3
% 21.95/12.95  #Sup     : 11695
% 21.95/12.95  #Fact    : 0
% 21.95/12.95  #Define  : 0
% 21.95/12.95  #Split   : 60
% 21.95/12.95  #Chain   : 0
% 21.95/12.95  #Close   : 0
% 21.95/12.95  
% 22.00/12.95  Ordering : KBO
% 22.00/12.95  
% 22.00/12.95  Simplification rules
% 22.00/12.95  ----------------------
% 22.00/12.95  #Subsume      : 3653
% 22.00/12.95  #Demod        : 3009
% 22.00/12.95  #Tautology    : 871
% 22.00/12.95  #SimpNegUnit  : 938
% 22.00/12.95  #BackRed      : 1738
% 22.00/12.95  
% 22.00/12.95  #Partial instantiations: 0
% 22.00/12.95  #Strategies tried      : 1
% 22.00/12.95  
% 22.00/12.95  Timing (in seconds)
% 22.00/12.95  ----------------------
% 22.00/12.95  Preprocessing        : 0.35
% 22.00/12.95  Parsing              : 0.19
% 22.00/12.95  CNF conversion       : 0.03
% 22.00/12.95  Main loop            : 11.83
% 22.00/12.95  Inferencing          : 2.02
% 22.00/12.95  Reduction            : 2.47
% 22.00/12.95  Demodulation         : 1.59
% 22.00/12.95  BG Simplification    : 0.22
% 22.00/12.95  Subsumption          : 6.21
% 22.00/12.95  Abstraction          : 0.34
% 22.00/12.95  MUC search           : 0.00
% 22.00/12.95  Cooper               : 0.00
% 22.00/12.96  Total                : 12.23
% 22.00/12.96  Index Insertion      : 0.00
% 22.00/12.96  Index Deletion       : 0.00
% 22.00/12.96  Index Matching       : 0.00
% 22.00/12.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
