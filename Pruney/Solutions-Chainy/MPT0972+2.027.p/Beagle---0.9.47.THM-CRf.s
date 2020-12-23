%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:38 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  168 (1299 expanded)
%              Number of leaves         :   31 ( 432 expanded)
%              Depth                    :   15
%              Number of atoms          :  330 (3868 expanded)
%              Number of equality atoms :  143 (1042 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_102,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_119,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_102])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_235,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_248,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_235])).

tff(c_269,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_288,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_269])).

tff(c_418,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_428,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_418])).

tff(c_441,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_288,c_428])).

tff(c_449,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_118,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_287,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_269])).

tff(c_425,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_418])).

tff(c_438,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287,c_425])).

tff(c_443,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_617,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_1'(A_118,B_119),k1_relat_1(A_118))
      | B_119 = A_118
      | k1_relat_1(B_119) != k1_relat_1(A_118)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_623,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_1'('#skF_4',B_119),'#skF_2')
      | B_119 = '#skF_4'
      | k1_relat_1(B_119) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_617])).

tff(c_672,plain,(
    ! [B_125] :
      ( r2_hidden('#skF_1'('#skF_4',B_125),'#skF_2')
      | B_125 = '#skF_4'
      | k1_relat_1(B_125) != '#skF_2'
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_58,c_443,c_623])).

tff(c_46,plain,(
    ! [E_31] :
      ( k1_funct_1('#skF_5',E_31) = k1_funct_1('#skF_4',E_31)
      | ~ r2_hidden(E_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_818,plain,(
    ! [B_139] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_139)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_139))
      | B_139 = '#skF_4'
      | k1_relat_1(B_139) != '#skF_2'
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_672,c_46])).

tff(c_20,plain,(
    ! [B_12,A_8] :
      ( k1_funct_1(B_12,'#skF_1'(A_8,B_12)) != k1_funct_1(A_8,'#skF_1'(A_8,B_12))
      | B_12 = A_8
      | k1_relat_1(B_12) != k1_relat_1(A_8)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_825,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_20])).

tff(c_832,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_52,c_449,c_118,c_58,c_449,c_443,c_825])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_845,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_44])).

tff(c_856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_845])).

tff(c_857,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_881,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_880,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_857,c_12])).

tff(c_89,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_89])).

tff(c_183,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_183])).

tff(c_213,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_906,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_213])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_906])).

tff(c_915,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_940,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_8])).

tff(c_939,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_915,c_12])).

tff(c_1000,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_213])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_1000])).

tff(c_1009,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_1015,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_48])).

tff(c_1150,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1184,plain,(
    ! [C_175] :
      ( k1_relset_1('#skF_2','#skF_3',C_175) = k1_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_1150])).

tff(c_1196,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1015,c_1184])).

tff(c_1286,plain,(
    ! [B_186,A_187,C_188] :
      ( k1_xboole_0 = B_186
      | k1_relset_1(A_187,B_186,C_188) = A_187
      | ~ v1_funct_2(C_188,A_187,B_186)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1289,plain,(
    ! [C_188] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_188) = '#skF_2'
      | ~ v1_funct_2(C_188,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_188,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_1286])).

tff(c_1397,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1289])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1022,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_10])).

tff(c_1100,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1022])).

tff(c_1413,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1100])).

tff(c_1474,plain,(
    ! [A_207] : k2_zfmisc_1(A_207,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1397,c_12])).

tff(c_1500,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_1009])).

tff(c_1517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1413,c_1500])).

tff(c_1520,plain,(
    ! [C_208] :
      ( k1_relset_1('#skF_2','#skF_3',C_208) = '#skF_2'
      | ~ v1_funct_2(C_208,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_208,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1289])).

tff(c_1526,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1015,c_1520])).

tff(c_1536,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1196,c_1526])).

tff(c_1014,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_54])).

tff(c_1195,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1014,c_1184])).

tff(c_1523,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1014,c_1520])).

tff(c_1533,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1195,c_1523])).

tff(c_1788,plain,(
    ! [A_233,B_234] :
      ( r2_hidden('#skF_1'(A_233,B_234),k1_relat_1(A_233))
      | B_234 = A_233
      | k1_relat_1(B_234) != k1_relat_1(A_233)
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234)
      | ~ v1_funct_1(A_233)
      | ~ v1_relat_1(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1794,plain,(
    ! [B_234] :
      ( r2_hidden('#skF_1'('#skF_4',B_234),'#skF_2')
      | B_234 = '#skF_4'
      | k1_relat_1(B_234) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_1788])).

tff(c_1889,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_1'('#skF_4',B_241),'#skF_2')
      | B_241 = '#skF_4'
      | k1_relat_1(B_241) != '#skF_2'
      | ~ v1_funct_1(B_241)
      | ~ v1_relat_1(B_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_58,c_1533,c_1794])).

tff(c_1893,plain,(
    ! [B_241] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_241)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_241))
      | B_241 = '#skF_4'
      | k1_relat_1(B_241) != '#skF_2'
      | ~ v1_funct_1(B_241)
      | ~ v1_relat_1(B_241) ) ),
    inference(resolution,[status(thm)],[c_1889,c_46])).

tff(c_1917,plain,(
    ! [B_244,A_245] :
      ( k1_funct_1(B_244,'#skF_1'(A_245,B_244)) != k1_funct_1(A_245,'#skF_1'(A_245,B_244))
      | B_244 = A_245
      | k1_relat_1(B_244) != k1_relat_1(A_245)
      | ~ v1_funct_1(B_244)
      | ~ v1_relat_1(B_244)
      | ~ v1_funct_1(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1921,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_1917])).

tff(c_1927,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_52,c_1536,c_118,c_58,c_1536,c_1533,c_1921])).

tff(c_101,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_89])).

tff(c_192,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_183])).

tff(c_212,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_1011,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_212])).

tff(c_1937,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1011])).

tff(c_1950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1937])).

tff(c_1952,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1022])).

tff(c_1973,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_8])).

tff(c_1982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1011])).

tff(c_1983,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_1988,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_48])).

tff(c_2144,plain,(
    ! [A_274,B_275,C_276] :
      ( k1_relset_1(A_274,B_275,C_276) = k1_relat_1(C_276)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2252,plain,(
    ! [C_291] :
      ( k1_relset_1('#skF_2','#skF_3',C_291) = k1_relat_1(C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_2144])).

tff(c_2264,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1988,c_2252])).

tff(c_2356,plain,(
    ! [B_302,A_303,C_304] :
      ( k1_xboole_0 = B_302
      | k1_relset_1(A_303,B_302,C_304) = A_303
      | ~ v1_funct_2(C_304,A_303,B_302)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2359,plain,(
    ! [C_304] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_304) = '#skF_2'
      | ~ v1_funct_2(C_304,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_304,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_2356])).

tff(c_2380,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2359])).

tff(c_1995,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_10])).

tff(c_2075,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1995])).

tff(c_2397,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2380,c_2075])).

tff(c_2406,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2380,c_2380,c_12])).

tff(c_2496,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_1983])).

tff(c_2498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2397,c_2496])).

tff(c_2501,plain,(
    ! [C_312] :
      ( k1_relset_1('#skF_2','#skF_3',C_312) = '#skF_2'
      | ~ v1_funct_2(C_312,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_312,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_2359])).

tff(c_2507,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1988,c_2501])).

tff(c_2517,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2264,c_2507])).

tff(c_1987,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_54])).

tff(c_2263,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1987,c_2252])).

tff(c_2504,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1987,c_2501])).

tff(c_2514,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2263,c_2504])).

tff(c_2797,plain,(
    ! [A_338,B_339] :
      ( r2_hidden('#skF_1'(A_338,B_339),k1_relat_1(A_338))
      | B_339 = A_338
      | k1_relat_1(B_339) != k1_relat_1(A_338)
      | ~ v1_funct_1(B_339)
      | ~ v1_relat_1(B_339)
      | ~ v1_funct_1(A_338)
      | ~ v1_relat_1(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2803,plain,(
    ! [B_339] :
      ( r2_hidden('#skF_1'('#skF_4',B_339),'#skF_2')
      | B_339 = '#skF_4'
      | k1_relat_1(B_339) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_339)
      | ~ v1_relat_1(B_339)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2514,c_2797])).

tff(c_2857,plain,(
    ! [B_342] :
      ( r2_hidden('#skF_1'('#skF_4',B_342),'#skF_2')
      | B_342 = '#skF_4'
      | k1_relat_1(B_342) != '#skF_2'
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_58,c_2514,c_2803])).

tff(c_2861,plain,(
    ! [B_342] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_342)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_342))
      | B_342 = '#skF_4'
      | k1_relat_1(B_342) != '#skF_2'
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342) ) ),
    inference(resolution,[status(thm)],[c_2857,c_46])).

tff(c_2890,plain,(
    ! [B_346,A_347] :
      ( k1_funct_1(B_346,'#skF_1'(A_347,B_346)) != k1_funct_1(A_347,'#skF_1'(A_347,B_346))
      | B_346 = A_347
      | k1_relat_1(B_346) != k1_relat_1(A_347)
      | ~ v1_funct_1(B_346)
      | ~ v1_relat_1(B_346)
      | ~ v1_funct_1(A_347)
      | ~ v1_relat_1(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2897,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2861,c_2890])).

tff(c_2902,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_52,c_2517,c_118,c_58,c_2517,c_2514,c_2897])).

tff(c_1986,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_100])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2011,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1986,c_2])).

tff(c_2036,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2011])).

tff(c_2919,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2902,c_2036])).

tff(c_2935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2919])).

tff(c_2937,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1995])).

tff(c_2947,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2937,c_8])).

tff(c_2956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_2036])).

tff(c_2957,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2011])).

tff(c_2959,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1983,c_193])).

tff(c_2960,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2959])).

tff(c_2980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2957,c_2960])).

tff(c_2981,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2959])).

tff(c_2990,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_44])).

tff(c_2986,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_2981,c_1988])).

tff(c_2987,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_1983])).

tff(c_3073,plain,(
    ! [A_351,B_352,D_353] :
      ( r2_relset_1(A_351,B_352,D_353,D_353)
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3110,plain,(
    ! [D_364] :
      ( r2_relset_1('#skF_2','#skF_3',D_364,D_364)
      | ~ m1_subset_1(D_364,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2987,c_3073])).

tff(c_3112,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2986,c_3110])).

tff(c_3119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2990,c_3112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.90  
% 4.66/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.90  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.66/1.90  
% 4.66/1.90  %Foreground sorts:
% 4.66/1.90  
% 4.66/1.90  
% 4.66/1.90  %Background operators:
% 4.66/1.90  
% 4.66/1.90  
% 4.66/1.90  %Foreground operators:
% 4.66/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.66/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.66/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.66/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.66/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.66/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.90  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.66/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.66/1.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.66/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.66/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.66/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.66/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.66/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.66/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.90  
% 4.66/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.66/1.92  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 4.66/1.92  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.66/1.92  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.66/1.92  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.66/1.92  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.66/1.92  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.66/1.92  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.66/1.92  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.66/1.92  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.66/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.92  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_102, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.66/1.92  tff(c_119, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_102])).
% 4.66/1.92  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_235, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.66/1.92  tff(c_248, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_235])).
% 4.66/1.92  tff(c_269, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.66/1.92  tff(c_288, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_269])).
% 4.66/1.92  tff(c_418, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.66/1.92  tff(c_428, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_418])).
% 4.66/1.92  tff(c_441, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_288, c_428])).
% 4.66/1.92  tff(c_449, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_441])).
% 4.66/1.92  tff(c_118, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_102])).
% 4.66/1.92  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_287, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_269])).
% 4.66/1.92  tff(c_425, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_418])).
% 4.66/1.92  tff(c_438, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287, c_425])).
% 4.66/1.92  tff(c_443, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_438])).
% 4.66/1.92  tff(c_617, plain, (![A_118, B_119]: (r2_hidden('#skF_1'(A_118, B_119), k1_relat_1(A_118)) | B_119=A_118 | k1_relat_1(B_119)!=k1_relat_1(A_118) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.92  tff(c_623, plain, (![B_119]: (r2_hidden('#skF_1'('#skF_4', B_119), '#skF_2') | B_119='#skF_4' | k1_relat_1(B_119)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_443, c_617])).
% 4.66/1.92  tff(c_672, plain, (![B_125]: (r2_hidden('#skF_1'('#skF_4', B_125), '#skF_2') | B_125='#skF_4' | k1_relat_1(B_125)!='#skF_2' | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_58, c_443, c_623])).
% 4.66/1.92  tff(c_46, plain, (![E_31]: (k1_funct_1('#skF_5', E_31)=k1_funct_1('#skF_4', E_31) | ~r2_hidden(E_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_818, plain, (![B_139]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_139))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_139)) | B_139='#skF_4' | k1_relat_1(B_139)!='#skF_2' | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_672, c_46])).
% 4.66/1.92  tff(c_20, plain, (![B_12, A_8]: (k1_funct_1(B_12, '#skF_1'(A_8, B_12))!=k1_funct_1(A_8, '#skF_1'(A_8, B_12)) | B_12=A_8 | k1_relat_1(B_12)!=k1_relat_1(A_8) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.92  tff(c_825, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_818, c_20])).
% 4.66/1.92  tff(c_832, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_52, c_449, c_118, c_58, c_449, c_443, c_825])).
% 4.66/1.92  tff(c_44, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.66/1.92  tff(c_845, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_832, c_44])).
% 4.66/1.92  tff(c_856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_845])).
% 4.66/1.92  tff(c_857, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_441])).
% 4.66/1.92  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.66/1.92  tff(c_881, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_857, c_8])).
% 4.66/1.92  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.92  tff(c_880, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_857, c_857, c_12])).
% 4.66/1.92  tff(c_89, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.92  tff(c_100, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_89])).
% 4.66/1.92  tff(c_183, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.92  tff(c_193, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_100, c_183])).
% 4.66/1.92  tff(c_213, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_193])).
% 4.66/1.92  tff(c_906, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_880, c_213])).
% 4.66/1.92  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_881, c_906])).
% 4.66/1.92  tff(c_915, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_438])).
% 4.66/1.92  tff(c_940, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_915, c_8])).
% 4.66/1.92  tff(c_939, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_915, c_915, c_12])).
% 4.66/1.92  tff(c_1000, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_939, c_213])).
% 4.66/1.92  tff(c_1008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_940, c_1000])).
% 4.66/1.92  tff(c_1009, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_193])).
% 4.66/1.92  tff(c_1015, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_48])).
% 4.66/1.92  tff(c_1150, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.66/1.92  tff(c_1184, plain, (![C_175]: (k1_relset_1('#skF_2', '#skF_3', C_175)=k1_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1009, c_1150])).
% 4.66/1.92  tff(c_1196, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1015, c_1184])).
% 4.66/1.92  tff(c_1286, plain, (![B_186, A_187, C_188]: (k1_xboole_0=B_186 | k1_relset_1(A_187, B_186, C_188)=A_187 | ~v1_funct_2(C_188, A_187, B_186) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.66/1.92  tff(c_1289, plain, (![C_188]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_188)='#skF_2' | ~v1_funct_2(C_188, '#skF_2', '#skF_3') | ~m1_subset_1(C_188, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1009, c_1286])).
% 4.66/1.92  tff(c_1397, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1289])).
% 4.66/1.92  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.92  tff(c_1022, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1009, c_10])).
% 4.66/1.92  tff(c_1100, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1022])).
% 4.66/1.92  tff(c_1413, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1100])).
% 4.66/1.92  tff(c_1474, plain, (![A_207]: (k2_zfmisc_1(A_207, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1397, c_12])).
% 4.66/1.92  tff(c_1500, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1474, c_1009])).
% 4.66/1.92  tff(c_1517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1413, c_1500])).
% 4.66/1.92  tff(c_1520, plain, (![C_208]: (k1_relset_1('#skF_2', '#skF_3', C_208)='#skF_2' | ~v1_funct_2(C_208, '#skF_2', '#skF_3') | ~m1_subset_1(C_208, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1289])).
% 4.66/1.92  tff(c_1526, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1015, c_1520])).
% 4.66/1.92  tff(c_1536, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1196, c_1526])).
% 4.66/1.92  tff(c_1014, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_54])).
% 4.66/1.92  tff(c_1195, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1014, c_1184])).
% 4.66/1.92  tff(c_1523, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1014, c_1520])).
% 4.66/1.92  tff(c_1533, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1195, c_1523])).
% 4.66/1.92  tff(c_1788, plain, (![A_233, B_234]: (r2_hidden('#skF_1'(A_233, B_234), k1_relat_1(A_233)) | B_234=A_233 | k1_relat_1(B_234)!=k1_relat_1(A_233) | ~v1_funct_1(B_234) | ~v1_relat_1(B_234) | ~v1_funct_1(A_233) | ~v1_relat_1(A_233))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.92  tff(c_1794, plain, (![B_234]: (r2_hidden('#skF_1'('#skF_4', B_234), '#skF_2') | B_234='#skF_4' | k1_relat_1(B_234)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_234) | ~v1_relat_1(B_234) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_1788])).
% 4.66/1.92  tff(c_1889, plain, (![B_241]: (r2_hidden('#skF_1'('#skF_4', B_241), '#skF_2') | B_241='#skF_4' | k1_relat_1(B_241)!='#skF_2' | ~v1_funct_1(B_241) | ~v1_relat_1(B_241))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_58, c_1533, c_1794])).
% 4.66/1.92  tff(c_1893, plain, (![B_241]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_241))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_241)) | B_241='#skF_4' | k1_relat_1(B_241)!='#skF_2' | ~v1_funct_1(B_241) | ~v1_relat_1(B_241))), inference(resolution, [status(thm)], [c_1889, c_46])).
% 4.66/1.92  tff(c_1917, plain, (![B_244, A_245]: (k1_funct_1(B_244, '#skF_1'(A_245, B_244))!=k1_funct_1(A_245, '#skF_1'(A_245, B_244)) | B_244=A_245 | k1_relat_1(B_244)!=k1_relat_1(A_245) | ~v1_funct_1(B_244) | ~v1_relat_1(B_244) | ~v1_funct_1(A_245) | ~v1_relat_1(A_245))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.92  tff(c_1921, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1893, c_1917])).
% 4.66/1.92  tff(c_1927, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_52, c_1536, c_118, c_58, c_1536, c_1533, c_1921])).
% 4.66/1.92  tff(c_101, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_89])).
% 4.66/1.92  tff(c_192, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_101, c_183])).
% 4.66/1.92  tff(c_212, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_192])).
% 4.66/1.92  tff(c_1011, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_212])).
% 4.66/1.92  tff(c_1937, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1011])).
% 4.66/1.92  tff(c_1950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1937])).
% 4.66/1.92  tff(c_1952, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1022])).
% 4.66/1.92  tff(c_1973, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_8])).
% 4.66/1.92  tff(c_1982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1011])).
% 4.66/1.92  tff(c_1983, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_192])).
% 4.66/1.92  tff(c_1988, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_48])).
% 4.66/1.92  tff(c_2144, plain, (![A_274, B_275, C_276]: (k1_relset_1(A_274, B_275, C_276)=k1_relat_1(C_276) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.66/1.92  tff(c_2252, plain, (![C_291]: (k1_relset_1('#skF_2', '#skF_3', C_291)=k1_relat_1(C_291) | ~m1_subset_1(C_291, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1983, c_2144])).
% 4.66/1.92  tff(c_2264, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1988, c_2252])).
% 4.66/1.92  tff(c_2356, plain, (![B_302, A_303, C_304]: (k1_xboole_0=B_302 | k1_relset_1(A_303, B_302, C_304)=A_303 | ~v1_funct_2(C_304, A_303, B_302) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.66/1.92  tff(c_2359, plain, (![C_304]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_304)='#skF_2' | ~v1_funct_2(C_304, '#skF_2', '#skF_3') | ~m1_subset_1(C_304, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1983, c_2356])).
% 4.66/1.92  tff(c_2380, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2359])).
% 4.66/1.92  tff(c_1995, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1983, c_10])).
% 4.66/1.92  tff(c_2075, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_1995])).
% 4.66/1.92  tff(c_2397, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2380, c_2075])).
% 4.66/1.92  tff(c_2406, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2380, c_2380, c_12])).
% 4.66/1.92  tff(c_2496, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_1983])).
% 4.66/1.92  tff(c_2498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2397, c_2496])).
% 4.66/1.92  tff(c_2501, plain, (![C_312]: (k1_relset_1('#skF_2', '#skF_3', C_312)='#skF_2' | ~v1_funct_2(C_312, '#skF_2', '#skF_3') | ~m1_subset_1(C_312, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_2359])).
% 4.66/1.92  tff(c_2507, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1988, c_2501])).
% 4.66/1.92  tff(c_2517, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2264, c_2507])).
% 4.66/1.92  tff(c_1987, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_54])).
% 4.66/1.92  tff(c_2263, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1987, c_2252])).
% 4.66/1.92  tff(c_2504, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1987, c_2501])).
% 4.66/1.92  tff(c_2514, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2263, c_2504])).
% 4.66/1.92  tff(c_2797, plain, (![A_338, B_339]: (r2_hidden('#skF_1'(A_338, B_339), k1_relat_1(A_338)) | B_339=A_338 | k1_relat_1(B_339)!=k1_relat_1(A_338) | ~v1_funct_1(B_339) | ~v1_relat_1(B_339) | ~v1_funct_1(A_338) | ~v1_relat_1(A_338))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.92  tff(c_2803, plain, (![B_339]: (r2_hidden('#skF_1'('#skF_4', B_339), '#skF_2') | B_339='#skF_4' | k1_relat_1(B_339)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_339) | ~v1_relat_1(B_339) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2514, c_2797])).
% 4.66/1.92  tff(c_2857, plain, (![B_342]: (r2_hidden('#skF_1'('#skF_4', B_342), '#skF_2') | B_342='#skF_4' | k1_relat_1(B_342)!='#skF_2' | ~v1_funct_1(B_342) | ~v1_relat_1(B_342))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_58, c_2514, c_2803])).
% 4.66/1.92  tff(c_2861, plain, (![B_342]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_342))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_342)) | B_342='#skF_4' | k1_relat_1(B_342)!='#skF_2' | ~v1_funct_1(B_342) | ~v1_relat_1(B_342))), inference(resolution, [status(thm)], [c_2857, c_46])).
% 4.66/1.92  tff(c_2890, plain, (![B_346, A_347]: (k1_funct_1(B_346, '#skF_1'(A_347, B_346))!=k1_funct_1(A_347, '#skF_1'(A_347, B_346)) | B_346=A_347 | k1_relat_1(B_346)!=k1_relat_1(A_347) | ~v1_funct_1(B_346) | ~v1_relat_1(B_346) | ~v1_funct_1(A_347) | ~v1_relat_1(A_347))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.92  tff(c_2897, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2861, c_2890])).
% 4.66/1.92  tff(c_2902, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_52, c_2517, c_118, c_58, c_2517, c_2514, c_2897])).
% 4.66/1.92  tff(c_1986, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_100])).
% 4.66/1.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.92  tff(c_2011, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1986, c_2])).
% 4.66/1.92  tff(c_2036, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2011])).
% 4.66/1.92  tff(c_2919, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2902, c_2036])).
% 4.66/1.92  tff(c_2935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2919])).
% 4.66/1.92  tff(c_2937, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1995])).
% 4.66/1.92  tff(c_2947, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2937, c_8])).
% 4.66/1.92  tff(c_2956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2947, c_2036])).
% 4.66/1.92  tff(c_2957, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2011])).
% 4.66/1.92  tff(c_2959, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1983, c_193])).
% 4.66/1.92  tff(c_2960, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2959])).
% 4.66/1.92  tff(c_2980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2957, c_2960])).
% 4.66/1.92  tff(c_2981, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2959])).
% 4.66/1.92  tff(c_2990, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_44])).
% 4.66/1.92  tff(c_2986, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_2981, c_1988])).
% 4.66/1.92  tff(c_2987, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_1983])).
% 4.66/1.92  tff(c_3073, plain, (![A_351, B_352, D_353]: (r2_relset_1(A_351, B_352, D_353, D_353) | ~m1_subset_1(D_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.66/1.92  tff(c_3110, plain, (![D_364]: (r2_relset_1('#skF_2', '#skF_3', D_364, D_364) | ~m1_subset_1(D_364, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2987, c_3073])).
% 4.66/1.92  tff(c_3112, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2986, c_3110])).
% 4.66/1.92  tff(c_3119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2990, c_3112])).
% 4.66/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.92  
% 4.66/1.92  Inference rules
% 4.66/1.92  ----------------------
% 4.66/1.92  #Ref     : 3
% 4.66/1.92  #Sup     : 606
% 4.66/1.92  #Fact    : 0
% 4.66/1.92  #Define  : 0
% 4.66/1.92  #Split   : 19
% 4.66/1.92  #Chain   : 0
% 4.66/1.92  #Close   : 0
% 4.66/1.92  
% 4.66/1.92  Ordering : KBO
% 4.66/1.92  
% 4.66/1.92  Simplification rules
% 4.66/1.92  ----------------------
% 4.66/1.92  #Subsume      : 84
% 4.66/1.92  #Demod        : 847
% 4.66/1.92  #Tautology    : 374
% 4.66/1.92  #SimpNegUnit  : 46
% 4.66/1.92  #BackRed      : 214
% 4.66/1.92  
% 4.66/1.92  #Partial instantiations: 0
% 4.66/1.92  #Strategies tried      : 1
% 4.66/1.92  
% 4.66/1.92  Timing (in seconds)
% 4.66/1.92  ----------------------
% 4.66/1.93  Preprocessing        : 0.34
% 4.66/1.93  Parsing              : 0.18
% 4.66/1.93  CNF conversion       : 0.02
% 4.66/1.93  Main loop            : 0.75
% 4.66/1.93  Inferencing          : 0.26
% 4.66/1.93  Reduction            : 0.25
% 4.66/1.93  Demodulation         : 0.17
% 4.66/1.93  BG Simplification    : 0.03
% 4.66/1.93  Subsumption          : 0.14
% 4.66/1.93  Abstraction          : 0.03
% 4.66/1.93  MUC search           : 0.00
% 4.66/1.93  Cooper               : 0.00
% 4.66/1.93  Total                : 1.14
% 4.66/1.93  Index Insertion      : 0.00
% 4.66/1.93  Index Deletion       : 0.00
% 4.66/1.93  Index Matching       : 0.00
% 4.66/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
