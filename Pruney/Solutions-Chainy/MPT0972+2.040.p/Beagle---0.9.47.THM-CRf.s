%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:40 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 355 expanded)
%              Number of leaves         :   38 ( 137 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 (1041 expanded)
%              Number of equality atoms :   57 ( 213 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_92,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_768,plain,(
    ! [C_157,B_158,A_159] :
      ( v1_xboole_0(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(B_158,A_159)))
      | ~ v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_785,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_768])).

tff(c_792,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_785])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_919,plain,(
    ! [A_183,B_184,D_185] :
      ( r2_relset_1(A_183,B_184,D_185,D_185)
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_936,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_919])).

tff(c_36,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_127,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_124])).

tff(c_136,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_127])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1110,plain,(
    ! [A_205,B_206,C_207] :
      ( k1_relset_1(A_205,B_206,C_207) = k1_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1137,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_1110])).

tff(c_1155,plain,(
    ! [B_210,A_211,C_212] :
      ( k1_xboole_0 = B_210
      | k1_relset_1(A_211,B_210,C_212) = A_211
      | ~ v1_funct_2(C_212,A_211,B_210)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1166,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1155])).

tff(c_1184,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1137,c_1166])).

tff(c_1191,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1184])).

tff(c_130,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_76,c_124])).

tff(c_139,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_130])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1138,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_1110])).

tff(c_1169,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1155])).

tff(c_1187,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1138,c_1169])).

tff(c_1216,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_1770,plain,(
    ! [A_268,B_269] :
      ( r2_hidden('#skF_3'(A_268,B_269),k1_relat_1(A_268))
      | B_269 = A_268
      | k1_relat_1(B_269) != k1_relat_1(A_268)
      | ~ v1_funct_1(B_269)
      | ~ v1_relat_1(B_269)
      | ~ v1_funct_1(A_268)
      | ~ v1_relat_1(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1781,plain,(
    ! [B_269] :
      ( r2_hidden('#skF_3'('#skF_6',B_269),'#skF_4')
      | B_269 = '#skF_6'
      | k1_relat_1(B_269) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_269)
      | ~ v1_relat_1(B_269)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1216,c_1770])).

tff(c_2562,plain,(
    ! [B_342] :
      ( r2_hidden('#skF_3'('#skF_6',B_342),'#skF_4')
      | B_342 = '#skF_6'
      | k1_relat_1(B_342) != '#skF_4'
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_80,c_1216,c_1781])).

tff(c_68,plain,(
    ! [E_52] :
      ( k1_funct_1('#skF_7',E_52) = k1_funct_1('#skF_6',E_52)
      | ~ r2_hidden(E_52,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2616,plain,(
    ! [B_345] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_345)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_345))
      | B_345 = '#skF_6'
      | k1_relat_1(B_345) != '#skF_4'
      | ~ v1_funct_1(B_345)
      | ~ v1_relat_1(B_345) ) ),
    inference(resolution,[status(thm)],[c_2562,c_68])).

tff(c_38,plain,(
    ! [B_29,A_25] :
      ( k1_funct_1(B_29,'#skF_3'(A_25,B_29)) != k1_funct_1(A_25,'#skF_3'(A_25,B_29))
      | B_29 = A_25
      | k1_relat_1(B_29) != k1_relat_1(A_25)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2623,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2616,c_38])).

tff(c_2630,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_1191,c_139,c_80,c_1191,c_1216,c_2623])).

tff(c_66,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2652,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2630,c_66])).

tff(c_2664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_2652])).

tff(c_2665,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2696,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2665,c_12])).

tff(c_2698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_2696])).

tff(c_2699,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_2730,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_12])).

tff(c_2732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_2730])).

tff(c_2734,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_785])).

tff(c_786,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_768])).

tff(c_2808,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_786])).

tff(c_167,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_190,plain,(
    ! [A_77,B_78] :
      ( ~ v1_xboole_0(A_77)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_194,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_190,c_14])).

tff(c_201,plain,(
    ! [B_73,A_72] :
      ( B_73 = A_72
      | ~ v1_xboole_0(B_73)
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_182,c_194])).

tff(c_2812,plain,(
    ! [A_354] :
      ( A_354 = '#skF_5'
      | ~ v1_xboole_0(A_354) ) ),
    inference(resolution,[status(thm)],[c_2734,c_201])).

tff(c_2819,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2808,c_2812])).

tff(c_2803,plain,(
    ! [A_351,B_352,D_353] :
      ( r2_relset_1(A_351,B_352,D_353,D_353)
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2806,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_2803])).

tff(c_2866,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_2806])).

tff(c_204,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ v1_xboole_0(B_81)
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_182,c_194])).

tff(c_207,plain,(
    ! [A_82] :
      ( k1_xboole_0 = A_82
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_12,c_204])).

tff(c_2747,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2734,c_207])).

tff(c_2733,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_785])).

tff(c_2740,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2733,c_207])).

tff(c_2776,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2747,c_2740])).

tff(c_2789,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2776,c_66])).

tff(c_2967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2866,c_2819,c_2819,c_2789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.94  
% 4.92/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.95  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.92/1.95  
% 4.92/1.95  %Foreground sorts:
% 4.92/1.95  
% 4.92/1.95  
% 4.92/1.95  %Background operators:
% 4.92/1.95  
% 4.92/1.95  
% 4.92/1.95  %Foreground operators:
% 4.92/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.92/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.92/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.92/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.92/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.92/1.95  tff('#skF_7', type, '#skF_7': $i).
% 4.92/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.92/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.92/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.92/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.92/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.92/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.92/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.92/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.92/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.92/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.92/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.92/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.92/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.92/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.92/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.95  
% 4.92/1.96  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.92/1.96  tff(f_105, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.92/1.96  tff(f_117, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.92/1.96  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.92/1.96  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.92/1.96  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.92/1.96  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.92/1.96  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.92/1.96  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.92/1.96  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.92/1.96  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.92/1.96  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.92/1.96  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.96  tff(c_768, plain, (![C_157, B_158, A_159]: (v1_xboole_0(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(B_158, A_159))) | ~v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.92/1.96  tff(c_785, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_768])).
% 4.92/1.97  tff(c_792, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_785])).
% 4.92/1.97  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.97  tff(c_919, plain, (![A_183, B_184, D_185]: (r2_relset_1(A_183, B_184, D_185, D_185) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.92/1.97  tff(c_936, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_76, c_919])).
% 4.92/1.97  tff(c_36, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.92/1.97  tff(c_124, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.92/1.97  tff(c_127, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_124])).
% 4.92/1.97  tff(c_136, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_127])).
% 4.92/1.97  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.97  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.97  tff(c_1110, plain, (![A_205, B_206, C_207]: (k1_relset_1(A_205, B_206, C_207)=k1_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.92/1.97  tff(c_1137, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_1110])).
% 4.92/1.97  tff(c_1155, plain, (![B_210, A_211, C_212]: (k1_xboole_0=B_210 | k1_relset_1(A_211, B_210, C_212)=A_211 | ~v1_funct_2(C_212, A_211, B_210) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.92/1.97  tff(c_1166, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_1155])).
% 4.92/1.97  tff(c_1184, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1137, c_1166])).
% 4.92/1.97  tff(c_1191, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1184])).
% 4.92/1.97  tff(c_130, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_76, c_124])).
% 4.92/1.97  tff(c_139, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_130])).
% 4.92/1.97  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.97  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.97  tff(c_1138, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_1110])).
% 4.92/1.97  tff(c_1169, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_1155])).
% 4.92/1.97  tff(c_1187, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1138, c_1169])).
% 4.92/1.97  tff(c_1216, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1187])).
% 4.92/1.97  tff(c_1770, plain, (![A_268, B_269]: (r2_hidden('#skF_3'(A_268, B_269), k1_relat_1(A_268)) | B_269=A_268 | k1_relat_1(B_269)!=k1_relat_1(A_268) | ~v1_funct_1(B_269) | ~v1_relat_1(B_269) | ~v1_funct_1(A_268) | ~v1_relat_1(A_268))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.92/1.97  tff(c_1781, plain, (![B_269]: (r2_hidden('#skF_3'('#skF_6', B_269), '#skF_4') | B_269='#skF_6' | k1_relat_1(B_269)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_269) | ~v1_relat_1(B_269) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1216, c_1770])).
% 4.92/1.97  tff(c_2562, plain, (![B_342]: (r2_hidden('#skF_3'('#skF_6', B_342), '#skF_4') | B_342='#skF_6' | k1_relat_1(B_342)!='#skF_4' | ~v1_funct_1(B_342) | ~v1_relat_1(B_342))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_80, c_1216, c_1781])).
% 4.92/1.97  tff(c_68, plain, (![E_52]: (k1_funct_1('#skF_7', E_52)=k1_funct_1('#skF_6', E_52) | ~r2_hidden(E_52, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.97  tff(c_2616, plain, (![B_345]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_345))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_345)) | B_345='#skF_6' | k1_relat_1(B_345)!='#skF_4' | ~v1_funct_1(B_345) | ~v1_relat_1(B_345))), inference(resolution, [status(thm)], [c_2562, c_68])).
% 4.92/1.97  tff(c_38, plain, (![B_29, A_25]: (k1_funct_1(B_29, '#skF_3'(A_25, B_29))!=k1_funct_1(A_25, '#skF_3'(A_25, B_29)) | B_29=A_25 | k1_relat_1(B_29)!=k1_relat_1(A_25) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.92/1.97  tff(c_2623, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2616, c_38])).
% 4.92/1.97  tff(c_2630, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_1191, c_139, c_80, c_1191, c_1216, c_2623])).
% 4.92/1.97  tff(c_66, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.92/1.97  tff(c_2652, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2630, c_66])).
% 4.92/1.97  tff(c_2664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_936, c_2652])).
% 4.92/1.97  tff(c_2665, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1187])).
% 4.92/1.97  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.92/1.97  tff(c_2696, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2665, c_12])).
% 4.92/1.97  tff(c_2698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_792, c_2696])).
% 4.92/1.97  tff(c_2699, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1184])).
% 4.92/1.97  tff(c_2730, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_12])).
% 4.92/1.97  tff(c_2732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_792, c_2730])).
% 4.92/1.97  tff(c_2734, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_785])).
% 4.92/1.97  tff(c_786, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_768])).
% 4.92/1.97  tff(c_2808, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_786])).
% 4.92/1.97  tff(c_167, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.92/1.97  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.92/1.97  tff(c_182, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_167, c_2])).
% 4.92/1.97  tff(c_190, plain, (![A_77, B_78]: (~v1_xboole_0(A_77) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_167, c_2])).
% 4.92/1.97  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.92/1.97  tff(c_194, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_190, c_14])).
% 4.92/1.97  tff(c_201, plain, (![B_73, A_72]: (B_73=A_72 | ~v1_xboole_0(B_73) | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_182, c_194])).
% 4.92/1.97  tff(c_2812, plain, (![A_354]: (A_354='#skF_5' | ~v1_xboole_0(A_354))), inference(resolution, [status(thm)], [c_2734, c_201])).
% 4.92/1.97  tff(c_2819, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2808, c_2812])).
% 4.92/1.97  tff(c_2803, plain, (![A_351, B_352, D_353]: (r2_relset_1(A_351, B_352, D_353, D_353) | ~m1_subset_1(D_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.92/1.97  tff(c_2806, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_76, c_2803])).
% 4.92/1.97  tff(c_2866, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_2806])).
% 4.92/1.97  tff(c_204, plain, (![B_81, A_82]: (B_81=A_82 | ~v1_xboole_0(B_81) | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_182, c_194])).
% 4.92/1.97  tff(c_207, plain, (![A_82]: (k1_xboole_0=A_82 | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_12, c_204])).
% 4.92/1.97  tff(c_2747, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2734, c_207])).
% 4.92/1.97  tff(c_2733, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_785])).
% 4.92/1.97  tff(c_2740, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2733, c_207])).
% 4.92/1.97  tff(c_2776, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2747, c_2740])).
% 4.92/1.97  tff(c_2789, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2776, c_66])).
% 4.92/1.97  tff(c_2967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2866, c_2819, c_2819, c_2789])).
% 4.92/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.97  
% 4.92/1.97  Inference rules
% 4.92/1.97  ----------------------
% 4.92/1.97  #Ref     : 1
% 4.92/1.97  #Sup     : 557
% 4.92/1.97  #Fact    : 0
% 4.92/1.97  #Define  : 0
% 4.92/1.97  #Split   : 14
% 4.92/1.97  #Chain   : 0
% 4.92/1.97  #Close   : 0
% 4.92/1.97  
% 4.92/1.97  Ordering : KBO
% 4.92/1.97  
% 4.92/1.97  Simplification rules
% 4.92/1.97  ----------------------
% 4.92/1.97  #Subsume      : 200
% 4.92/1.97  #Demod        : 543
% 4.92/1.97  #Tautology    : 267
% 4.92/1.97  #SimpNegUnit  : 75
% 4.92/1.97  #BackRed      : 201
% 4.92/1.97  
% 4.92/1.97  #Partial instantiations: 0
% 4.92/1.97  #Strategies tried      : 1
% 4.92/1.97  
% 4.92/1.97  Timing (in seconds)
% 4.92/1.97  ----------------------
% 4.92/1.97  Preprocessing        : 0.37
% 4.92/1.97  Parsing              : 0.20
% 4.92/1.97  CNF conversion       : 0.03
% 4.92/1.97  Main loop            : 0.78
% 4.92/1.97  Inferencing          : 0.25
% 4.92/1.97  Reduction            : 0.26
% 4.92/1.97  Demodulation         : 0.18
% 4.92/1.97  BG Simplification    : 0.03
% 4.92/1.97  Subsumption          : 0.16
% 4.92/1.97  Abstraction          : 0.03
% 4.92/1.97  MUC search           : 0.00
% 4.92/1.97  Cooper               : 0.00
% 4.92/1.97  Total                : 1.19
% 4.92/1.97  Index Insertion      : 0.00
% 4.92/1.97  Index Deletion       : 0.00
% 4.92/1.97  Index Matching       : 0.00
% 4.92/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
