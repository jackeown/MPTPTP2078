%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:44 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 315 expanded)
%              Number of leaves         :   35 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 (1035 expanded)
%              Number of equality atoms :   53 ( 251 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2091,plain,(
    ! [A_233,B_234] :
      ( r2_hidden('#skF_1'(A_233,B_234),A_233)
      | r1_tarski(A_233,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2099,plain,(
    ! [A_233] : r1_tarski(A_233,A_233) ),
    inference(resolution,[status(thm)],[c_2091,c_4])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_75,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_85,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_81])).

tff(c_176,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_185,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_176])).

tff(c_250,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k1_relset_1(A_89,B_90,C_91),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_269,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_250])).

tff(c_274,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_269])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_282,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_274,c_10])).

tff(c_144,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_3'(A_65),k1_relat_1(A_65))
      | v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2002,plain,(
    ! [A_215,B_216] :
      ( r2_hidden('#skF_3'(A_215),B_216)
      | ~ r1_tarski(k1_relat_1(A_215),B_216)
      | v2_funct_1(A_215)
      | ~ v1_funct_1(A_215)
      | ~ v1_relat_1(A_215) ) ),
    inference(resolution,[status(thm)],[c_144,c_2])).

tff(c_137,plain,(
    ! [A_64] :
      ( '#skF_2'(A_64) != '#skF_3'(A_64)
      | v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_62])).

tff(c_143,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_140])).

tff(c_153,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_2'(A_66),k1_relat_1(A_66))
      | v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1138,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_2'(A_151),B_152)
      | ~ r1_tarski(k1_relat_1(A_151),B_152)
      | v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_283,plain,(
    ! [A_92] :
      ( k1_funct_1(A_92,'#skF_2'(A_92)) = k1_funct_1(A_92,'#skF_3'(A_92))
      | v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ! [D_38,C_37] :
      ( v2_funct_1('#skF_5')
      | D_38 = C_37
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5',C_37)
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_213,plain,(
    ! [D_38,C_37] :
      ( D_38 = C_37
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5',C_37)
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60])).

tff(c_289,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_213])).

tff(c_298,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_289])).

tff(c_299,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_298])).

tff(c_511,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_1143,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1138,c_511])).

tff(c_1152,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_282,c_1143])).

tff(c_1154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1152])).

tff(c_1156,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_292,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_213])).

tff(c_301,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_292])).

tff(c_302,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_301])).

tff(c_1173,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_38,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_302])).

tff(c_1176,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1173])).

tff(c_1177,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_1176])).

tff(c_2007,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2002,c_1177])).

tff(c_2016,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_282,c_2007])).

tff(c_2018,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2016])).

tff(c_2020,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2046,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_44])).

tff(c_46,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2023,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_46])).

tff(c_2569,plain,(
    ! [D_292,C_293,B_294,A_295] :
      ( k1_funct_1(k2_funct_1(D_292),k1_funct_1(D_292,C_293)) = C_293
      | k1_xboole_0 = B_294
      | ~ r2_hidden(C_293,A_295)
      | ~ v2_funct_1(D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(A_295,B_294)))
      | ~ v1_funct_2(D_292,A_295,B_294)
      | ~ v1_funct_1(D_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2596,plain,(
    ! [D_296,B_297] :
      ( k1_funct_1(k2_funct_1(D_296),k1_funct_1(D_296,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_297
      | ~ v2_funct_1(D_296)
      | ~ m1_subset_1(D_296,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_297)))
      | ~ v1_funct_2(D_296,'#skF_4',B_297)
      | ~ v1_funct_1(D_296) ) ),
    inference(resolution,[status(thm)],[c_2023,c_2569])).

tff(c_2610,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2596])).

tff(c_2617,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2020,c_2046,c_2610])).

tff(c_2639,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2617])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2025,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_48])).

tff(c_2114,plain,(
    ! [C_238,B_239,A_240] :
      ( r2_hidden(C_238,B_239)
      | ~ r2_hidden(C_238,A_240)
      | ~ r1_tarski(A_240,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2124,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_6',B_241)
      | ~ r1_tarski('#skF_4',B_241) ) ),
    inference(resolution,[status(thm)],[c_2025,c_2114])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2141,plain,(
    ! [B_244] :
      ( ~ r1_tarski(B_244,'#skF_6')
      | ~ r1_tarski('#skF_4',B_244) ) ),
    inference(resolution,[status(thm)],[c_2124,c_28])).

tff(c_2149,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_2141])).

tff(c_2657,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2639,c_2149])).

tff(c_2662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_2657])).

tff(c_2664,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2617])).

tff(c_2019,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2663,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2617])).

tff(c_2786,plain,(
    ! [D_307,B_308] :
      ( k1_funct_1(k2_funct_1(D_307),k1_funct_1(D_307,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_308
      | ~ v2_funct_1(D_307)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_308)))
      | ~ v1_funct_2(D_307,'#skF_4',B_308)
      | ~ v1_funct_1(D_307) ) ),
    inference(resolution,[status(thm)],[c_2025,c_2569])).

tff(c_2800,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2786])).

tff(c_2807,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2020,c_2663,c_2800])).

tff(c_2809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2664,c_2019,c_2807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.88  
% 4.65/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.89  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.65/1.89  
% 4.65/1.89  %Foreground sorts:
% 4.65/1.89  
% 4.65/1.89  
% 4.65/1.89  %Background operators:
% 4.65/1.89  
% 4.65/1.89  
% 4.65/1.89  %Foreground operators:
% 4.65/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.65/1.89  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.65/1.89  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.65/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.65/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.65/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.65/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.65/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.65/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.65/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.65/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.65/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.65/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.65/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.65/1.89  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.65/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.65/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.65/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.89  
% 4.65/1.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.65/1.91  tff(f_107, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 4.65/1.91  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.65/1.91  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.65/1.91  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.65/1.91  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.65/1.91  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.65/1.91  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 4.65/1.91  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 4.65/1.91  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.65/1.91  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.65/1.91  tff(c_2091, plain, (![A_233, B_234]: (r2_hidden('#skF_1'(A_233, B_234), A_233) | r1_tarski(A_233, B_234))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.91  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.91  tff(c_2099, plain, (![A_233]: (r1_tarski(A_233, A_233))), inference(resolution, [status(thm)], [c_2091, c_4])).
% 4.65/1.91  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_42, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_62, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_42])).
% 4.65/1.91  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.65/1.91  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_75, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.65/1.91  tff(c_81, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_75])).
% 4.65/1.91  tff(c_85, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_81])).
% 4.65/1.91  tff(c_176, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.65/1.91  tff(c_185, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_176])).
% 4.65/1.91  tff(c_250, plain, (![A_89, B_90, C_91]: (m1_subset_1(k1_relset_1(A_89, B_90, C_91), k1_zfmisc_1(A_89)) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.65/1.91  tff(c_269, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_185, c_250])).
% 4.65/1.91  tff(c_274, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_269])).
% 4.65/1.91  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.65/1.91  tff(c_282, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_274, c_10])).
% 4.65/1.91  tff(c_144, plain, (![A_65]: (r2_hidden('#skF_3'(A_65), k1_relat_1(A_65)) | v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.65/1.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.91  tff(c_2002, plain, (![A_215, B_216]: (r2_hidden('#skF_3'(A_215), B_216) | ~r1_tarski(k1_relat_1(A_215), B_216) | v2_funct_1(A_215) | ~v1_funct_1(A_215) | ~v1_relat_1(A_215))), inference(resolution, [status(thm)], [c_144, c_2])).
% 4.65/1.91  tff(c_137, plain, (![A_64]: ('#skF_2'(A_64)!='#skF_3'(A_64) | v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.65/1.91  tff(c_140, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_137, c_62])).
% 4.65/1.91  tff(c_143, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_140])).
% 4.65/1.91  tff(c_153, plain, (![A_66]: (r2_hidden('#skF_2'(A_66), k1_relat_1(A_66)) | v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.65/1.91  tff(c_1138, plain, (![A_151, B_152]: (r2_hidden('#skF_2'(A_151), B_152) | ~r1_tarski(k1_relat_1(A_151), B_152) | v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_153, c_2])).
% 4.65/1.91  tff(c_283, plain, (![A_92]: (k1_funct_1(A_92, '#skF_2'(A_92))=k1_funct_1(A_92, '#skF_3'(A_92)) | v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.65/1.91  tff(c_60, plain, (![D_38, C_37]: (v2_funct_1('#skF_5') | D_38=C_37 | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', C_37) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_213, plain, (![D_38, C_37]: (D_38=C_37 | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', C_37) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_60])).
% 4.65/1.91  tff(c_289, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_213])).
% 4.65/1.91  tff(c_298, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_289])).
% 4.65/1.91  tff(c_299, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_298])).
% 4.65/1.91  tff(c_511, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_299])).
% 4.65/1.91  tff(c_1143, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1138, c_511])).
% 4.65/1.91  tff(c_1152, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_282, c_1143])).
% 4.65/1.91  tff(c_1154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1152])).
% 4.65/1.91  tff(c_1156, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_299])).
% 4.65/1.91  tff(c_292, plain, (![D_38]: (D_38='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_213])).
% 4.65/1.91  tff(c_301, plain, (![D_38]: (D_38='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_292])).
% 4.65/1.91  tff(c_302, plain, (![D_38]: (D_38='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_301])).
% 4.65/1.91  tff(c_1173, plain, (![D_38]: (D_38='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_38, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_302])).
% 4.65/1.91  tff(c_1176, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_1173])).
% 4.65/1.91  tff(c_1177, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_143, c_1176])).
% 4.65/1.91  tff(c_2007, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2002, c_1177])).
% 4.65/1.91  tff(c_2016, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_282, c_2007])).
% 4.65/1.91  tff(c_2018, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2016])).
% 4.65/1.91  tff(c_2020, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 4.65/1.91  tff(c_44, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_2046, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_44])).
% 4.65/1.91  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_2023, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_46])).
% 4.65/1.91  tff(c_2569, plain, (![D_292, C_293, B_294, A_295]: (k1_funct_1(k2_funct_1(D_292), k1_funct_1(D_292, C_293))=C_293 | k1_xboole_0=B_294 | ~r2_hidden(C_293, A_295) | ~v2_funct_1(D_292) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(A_295, B_294))) | ~v1_funct_2(D_292, A_295, B_294) | ~v1_funct_1(D_292))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.65/1.91  tff(c_2596, plain, (![D_296, B_297]: (k1_funct_1(k2_funct_1(D_296), k1_funct_1(D_296, '#skF_7'))='#skF_7' | k1_xboole_0=B_297 | ~v2_funct_1(D_296) | ~m1_subset_1(D_296, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_297))) | ~v1_funct_2(D_296, '#skF_4', B_297) | ~v1_funct_1(D_296))), inference(resolution, [status(thm)], [c_2023, c_2569])).
% 4.65/1.91  tff(c_2610, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2596])).
% 4.65/1.91  tff(c_2617, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2020, c_2046, c_2610])).
% 4.65/1.91  tff(c_2639, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2617])).
% 4.65/1.91  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.65/1.91  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.65/1.91  tff(c_2025, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_48])).
% 4.65/1.91  tff(c_2114, plain, (![C_238, B_239, A_240]: (r2_hidden(C_238, B_239) | ~r2_hidden(C_238, A_240) | ~r1_tarski(A_240, B_239))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.91  tff(c_2124, plain, (![B_241]: (r2_hidden('#skF_6', B_241) | ~r1_tarski('#skF_4', B_241))), inference(resolution, [status(thm)], [c_2025, c_2114])).
% 4.65/1.91  tff(c_28, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.65/1.91  tff(c_2141, plain, (![B_244]: (~r1_tarski(B_244, '#skF_6') | ~r1_tarski('#skF_4', B_244))), inference(resolution, [status(thm)], [c_2124, c_28])).
% 4.65/1.91  tff(c_2149, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2141])).
% 4.65/1.91  tff(c_2657, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2639, c_2149])).
% 4.65/1.91  tff(c_2662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2099, c_2657])).
% 4.65/1.91  tff(c_2664, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2617])).
% 4.65/1.91  tff(c_2019, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 4.65/1.91  tff(c_2663, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7'), inference(splitRight, [status(thm)], [c_2617])).
% 4.65/1.91  tff(c_2786, plain, (![D_307, B_308]: (k1_funct_1(k2_funct_1(D_307), k1_funct_1(D_307, '#skF_6'))='#skF_6' | k1_xboole_0=B_308 | ~v2_funct_1(D_307) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_308))) | ~v1_funct_2(D_307, '#skF_4', B_308) | ~v1_funct_1(D_307))), inference(resolution, [status(thm)], [c_2025, c_2569])).
% 4.65/1.91  tff(c_2800, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2786])).
% 4.65/1.91  tff(c_2807, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2020, c_2663, c_2800])).
% 4.65/1.91  tff(c_2809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2664, c_2019, c_2807])).
% 4.65/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.91  
% 4.65/1.91  Inference rules
% 4.65/1.91  ----------------------
% 4.65/1.91  #Ref     : 6
% 4.65/1.91  #Sup     : 538
% 4.65/1.91  #Fact    : 0
% 4.65/1.91  #Define  : 0
% 4.65/1.91  #Split   : 28
% 4.65/1.91  #Chain   : 0
% 4.65/1.91  #Close   : 0
% 4.65/1.91  
% 4.65/1.91  Ordering : KBO
% 4.65/1.91  
% 4.65/1.91  Simplification rules
% 4.65/1.91  ----------------------
% 4.65/1.91  #Subsume      : 172
% 4.65/1.91  #Demod        : 281
% 4.65/1.91  #Tautology    : 190
% 4.65/1.91  #SimpNegUnit  : 96
% 4.65/1.91  #BackRed      : 74
% 4.65/1.91  
% 4.65/1.91  #Partial instantiations: 0
% 4.65/1.91  #Strategies tried      : 1
% 4.65/1.91  
% 4.65/1.91  Timing (in seconds)
% 4.65/1.91  ----------------------
% 4.65/1.91  Preprocessing        : 0.34
% 4.65/1.91  Parsing              : 0.18
% 4.65/1.91  CNF conversion       : 0.02
% 4.65/1.91  Main loop            : 0.77
% 4.65/1.91  Inferencing          : 0.26
% 4.65/1.91  Reduction            : 0.25
% 4.65/1.91  Demodulation         : 0.18
% 4.65/1.91  BG Simplification    : 0.03
% 4.65/1.91  Subsumption          : 0.14
% 4.65/1.91  Abstraction          : 0.03
% 4.65/1.91  MUC search           : 0.00
% 4.65/1.91  Cooper               : 0.00
% 4.65/1.91  Total                : 1.15
% 4.65/1.91  Index Insertion      : 0.00
% 4.65/1.91  Index Deletion       : 0.00
% 4.65/1.91  Index Matching       : 0.00
% 4.65/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
