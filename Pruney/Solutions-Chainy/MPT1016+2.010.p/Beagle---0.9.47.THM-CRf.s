%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:42 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 311 expanded)
%              Number of leaves         :   35 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  218 (1076 expanded)
%              Number of equality atoms :   54 ( 277 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_63,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_84,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_118,plain,(
    ! [A_62] :
      ( '#skF_2'(A_62) != '#skF_1'(A_62)
      | v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_121,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_63])).

tff(c_124,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40,c_121])).

tff(c_230,plain,(
    ! [A_81] :
      ( k1_funct_1(A_81,'#skF_2'(A_81)) = k1_funct_1(A_81,'#skF_1'(A_81))
      | v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    ! [D_37,C_36] :
      ( v2_funct_1('#skF_4')
      | D_37 = C_36
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4',C_36)
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_125,plain,(
    ! [D_37,C_36] :
      ( D_37 = C_36
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4',C_36)
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_60])).

tff(c_239,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_125])).

tff(c_248,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40,c_239])).

tff(c_249,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_248])).

tff(c_337,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_145,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_154,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_145])).

tff(c_170,plain,(
    ! [A_73,B_74,C_75] :
      ( m1_subset_1(k1_relset_1(A_73,B_74,C_75),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_186,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_170])).

tff(c_192,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_186])).

tff(c_131,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_2'(A_65),k1_relat_1(A_65))
      | v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_589,plain,(
    ! [A_157,A_158] :
      ( r2_hidden('#skF_2'(A_157),A_158)
      | ~ m1_subset_1(k1_relat_1(A_157),k1_zfmisc_1(A_158))
      | v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(resolution,[status(thm)],[c_131,c_10])).

tff(c_592,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_589])).

tff(c_599,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40,c_592])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_337,c_599])).

tff(c_603,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_236,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_125])).

tff(c_245,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40,c_236])).

tff(c_246,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_245])).

tff(c_604,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_604])).

tff(c_613,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_672,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_613])).

tff(c_673,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_672])).

tff(c_138,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_1'(A_66),k1_relat_1(A_66))
      | v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_880,plain,(
    ! [A_208,A_209] :
      ( r2_hidden('#skF_1'(A_208),A_209)
      | ~ m1_subset_1(k1_relat_1(A_208),k1_zfmisc_1(A_209))
      | v2_funct_1(A_208)
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_138,c_10])).

tff(c_883,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_880])).

tff(c_890,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_40,c_883])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_673,c_890])).

tff(c_894,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_898,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_48])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_935,plain,(
    ! [C_219,B_220,A_221] :
      ( ~ v1_xboole_0(C_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(C_219))
      | ~ r2_hidden(A_221,B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_955,plain,(
    ! [B_227,A_228,A_229] :
      ( ~ v1_xboole_0(B_227)
      | ~ r2_hidden(A_228,A_229)
      | ~ r1_tarski(A_229,B_227) ) ),
    inference(resolution,[status(thm)],[c_14,c_935])).

tff(c_962,plain,(
    ! [B_230] :
      ( ~ v1_xboole_0(B_230)
      | ~ r1_tarski('#skF_3',B_230) ) ),
    inference(resolution,[status(thm)],[c_898,c_955])).

tff(c_967,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_962])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_900,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_44])).

tff(c_1317,plain,(
    ! [D_300,C_301,B_302,A_303] :
      ( k1_funct_1(k2_funct_1(D_300),k1_funct_1(D_300,C_301)) = C_301
      | k1_xboole_0 = B_302
      | ~ r2_hidden(C_301,A_303)
      | ~ v2_funct_1(D_300)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302)))
      | ~ v1_funct_2(D_300,A_303,B_302)
      | ~ v1_funct_1(D_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1348,plain,(
    ! [D_312,B_313] :
      ( k1_funct_1(k2_funct_1(D_312),k1_funct_1(D_312,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_313
      | ~ v2_funct_1(D_312)
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_313)))
      | ~ v1_funct_2(D_312,'#skF_3',B_313)
      | ~ v1_funct_1(D_312) ) ),
    inference(resolution,[status(thm)],[c_898,c_1317])).

tff(c_1356,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1348])).

tff(c_1361,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_894,c_900,c_1356])).

tff(c_1362,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1361])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1365,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_2])).

tff(c_1367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_967,c_1365])).

tff(c_1369,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1361])).

tff(c_893,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1368,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1361])).

tff(c_46,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_896,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_46])).

tff(c_1437,plain,(
    ! [D_324,B_325] :
      ( k1_funct_1(k2_funct_1(D_324),k1_funct_1(D_324,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_325
      | ~ v2_funct_1(D_324)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_325)))
      | ~ v1_funct_2(D_324,'#skF_3',B_325)
      | ~ v1_funct_1(D_324) ) ),
    inference(resolution,[status(thm)],[c_896,c_1317])).

tff(c_1445,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1437])).

tff(c_1450,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_894,c_1368,c_1445])).

tff(c_1452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1369,c_893,c_1450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:16:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.61  
% 3.52/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.61  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.52/1.61  
% 3.52/1.61  %Foreground sorts:
% 3.52/1.61  
% 3.52/1.61  
% 3.52/1.61  %Background operators:
% 3.52/1.61  
% 3.52/1.61  
% 3.52/1.61  %Foreground operators:
% 3.52/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.52/1.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.52/1.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.52/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.52/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.52/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.61  
% 3.95/1.63  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.63  tff(f_109, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 3.95/1.63  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.95/1.63  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.95/1.63  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.95/1.63  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.95/1.63  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.95/1.63  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.95/1.63  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.95/1.63  tff(f_91, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.95/1.63  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.95/1.63  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.95/1.63  tff(c_42, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_63, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 3.95/1.63  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_84, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.95/1.63  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_84])).
% 3.95/1.63  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_118, plain, (![A_62]: ('#skF_2'(A_62)!='#skF_1'(A_62) | v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.63  tff(c_121, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_118, c_63])).
% 3.95/1.63  tff(c_124, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40, c_121])).
% 3.95/1.63  tff(c_230, plain, (![A_81]: (k1_funct_1(A_81, '#skF_2'(A_81))=k1_funct_1(A_81, '#skF_1'(A_81)) | v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.63  tff(c_60, plain, (![D_37, C_36]: (v2_funct_1('#skF_4') | D_37=C_36 | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', C_36) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_125, plain, (![D_37, C_36]: (D_37=C_36 | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', C_36) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_60])).
% 3.95/1.63  tff(c_239, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_125])).
% 3.95/1.63  tff(c_248, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40, c_239])).
% 3.95/1.63  tff(c_249, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_248])).
% 3.95/1.63  tff(c_337, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_249])).
% 3.95/1.63  tff(c_145, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.95/1.63  tff(c_154, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_145])).
% 3.95/1.63  tff(c_170, plain, (![A_73, B_74, C_75]: (m1_subset_1(k1_relset_1(A_73, B_74, C_75), k1_zfmisc_1(A_73)) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.95/1.63  tff(c_186, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_154, c_170])).
% 3.95/1.63  tff(c_192, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_186])).
% 3.95/1.63  tff(c_131, plain, (![A_65]: (r2_hidden('#skF_2'(A_65), k1_relat_1(A_65)) | v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.63  tff(c_10, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.63  tff(c_589, plain, (![A_157, A_158]: (r2_hidden('#skF_2'(A_157), A_158) | ~m1_subset_1(k1_relat_1(A_157), k1_zfmisc_1(A_158)) | v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(resolution, [status(thm)], [c_131, c_10])).
% 3.95/1.63  tff(c_592, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_589])).
% 3.95/1.63  tff(c_599, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40, c_592])).
% 3.95/1.63  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_337, c_599])).
% 3.95/1.63  tff(c_603, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_249])).
% 3.95/1.63  tff(c_236, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_125])).
% 3.95/1.63  tff(c_245, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40, c_236])).
% 3.95/1.63  tff(c_246, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_245])).
% 3.95/1.63  tff(c_604, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_246])).
% 3.95/1.63  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_603, c_604])).
% 3.95/1.63  tff(c_613, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_36, '#skF_3'))), inference(splitRight, [status(thm)], [c_246])).
% 3.95/1.63  tff(c_672, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_613])).
% 3.95/1.63  tff(c_673, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_124, c_672])).
% 3.95/1.63  tff(c_138, plain, (![A_66]: (r2_hidden('#skF_1'(A_66), k1_relat_1(A_66)) | v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.63  tff(c_880, plain, (![A_208, A_209]: (r2_hidden('#skF_1'(A_208), A_209) | ~m1_subset_1(k1_relat_1(A_208), k1_zfmisc_1(A_209)) | v2_funct_1(A_208) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_138, c_10])).
% 3.95/1.63  tff(c_883, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_880])).
% 3.95/1.63  tff(c_890, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_40, c_883])).
% 3.95/1.63  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_673, c_890])).
% 3.95/1.63  tff(c_894, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 3.95/1.63  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_898, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_48])).
% 3.95/1.63  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.63  tff(c_935, plain, (![C_219, B_220, A_221]: (~v1_xboole_0(C_219) | ~m1_subset_1(B_220, k1_zfmisc_1(C_219)) | ~r2_hidden(A_221, B_220))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.95/1.63  tff(c_955, plain, (![B_227, A_228, A_229]: (~v1_xboole_0(B_227) | ~r2_hidden(A_228, A_229) | ~r1_tarski(A_229, B_227))), inference(resolution, [status(thm)], [c_14, c_935])).
% 3.95/1.63  tff(c_962, plain, (![B_230]: (~v1_xboole_0(B_230) | ~r1_tarski('#skF_3', B_230))), inference(resolution, [status(thm)], [c_898, c_955])).
% 3.95/1.63  tff(c_967, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_962])).
% 3.95/1.63  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_44, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_900, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_44])).
% 3.95/1.63  tff(c_1317, plain, (![D_300, C_301, B_302, A_303]: (k1_funct_1(k2_funct_1(D_300), k1_funct_1(D_300, C_301))=C_301 | k1_xboole_0=B_302 | ~r2_hidden(C_301, A_303) | ~v2_funct_1(D_300) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))) | ~v1_funct_2(D_300, A_303, B_302) | ~v1_funct_1(D_300))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.63  tff(c_1348, plain, (![D_312, B_313]: (k1_funct_1(k2_funct_1(D_312), k1_funct_1(D_312, '#skF_5'))='#skF_5' | k1_xboole_0=B_313 | ~v2_funct_1(D_312) | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_313))) | ~v1_funct_2(D_312, '#skF_3', B_313) | ~v1_funct_1(D_312))), inference(resolution, [status(thm)], [c_898, c_1317])).
% 3.95/1.63  tff(c_1356, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1348])).
% 3.95/1.63  tff(c_1361, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_894, c_900, c_1356])).
% 3.95/1.63  tff(c_1362, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1361])).
% 3.95/1.63  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.95/1.63  tff(c_1365, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_2])).
% 3.95/1.63  tff(c_1367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_967, c_1365])).
% 3.95/1.63  tff(c_1369, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1361])).
% 3.95/1.63  tff(c_893, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 3.95/1.63  tff(c_1368, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1361])).
% 3.95/1.63  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.95/1.63  tff(c_896, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_46])).
% 3.95/1.63  tff(c_1437, plain, (![D_324, B_325]: (k1_funct_1(k2_funct_1(D_324), k1_funct_1(D_324, '#skF_6'))='#skF_6' | k1_xboole_0=B_325 | ~v2_funct_1(D_324) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_325))) | ~v1_funct_2(D_324, '#skF_3', B_325) | ~v1_funct_1(D_324))), inference(resolution, [status(thm)], [c_896, c_1317])).
% 3.95/1.63  tff(c_1445, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1437])).
% 3.95/1.63  tff(c_1450, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_894, c_1368, c_1445])).
% 3.95/1.63  tff(c_1452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1369, c_893, c_1450])).
% 3.95/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.63  
% 3.95/1.63  Inference rules
% 3.95/1.63  ----------------------
% 3.95/1.63  #Ref     : 5
% 3.95/1.63  #Sup     : 309
% 3.95/1.63  #Fact    : 0
% 3.95/1.63  #Define  : 0
% 3.95/1.63  #Split   : 16
% 3.95/1.63  #Chain   : 0
% 3.95/1.63  #Close   : 0
% 3.95/1.63  
% 3.95/1.63  Ordering : KBO
% 3.95/1.63  
% 3.95/1.63  Simplification rules
% 3.95/1.63  ----------------------
% 3.95/1.63  #Subsume      : 75
% 3.95/1.63  #Demod        : 108
% 3.95/1.63  #Tautology    : 55
% 3.95/1.63  #SimpNegUnit  : 12
% 3.95/1.63  #BackRed      : 3
% 3.95/1.63  
% 3.95/1.63  #Partial instantiations: 0
% 3.95/1.63  #Strategies tried      : 1
% 3.95/1.63  
% 3.95/1.63  Timing (in seconds)
% 3.95/1.63  ----------------------
% 3.95/1.63  Preprocessing        : 0.34
% 3.95/1.63  Parsing              : 0.17
% 3.95/1.63  CNF conversion       : 0.02
% 3.95/1.63  Main loop            : 0.51
% 3.95/1.63  Inferencing          : 0.19
% 3.95/1.63  Reduction            : 0.15
% 3.95/1.63  Demodulation         : 0.10
% 3.95/1.63  BG Simplification    : 0.03
% 3.95/1.63  Subsumption          : 0.11
% 3.95/1.63  Abstraction          : 0.02
% 3.95/1.63  MUC search           : 0.00
% 3.95/1.63  Cooper               : 0.00
% 3.95/1.63  Total                : 0.89
% 3.95/1.63  Index Insertion      : 0.00
% 3.95/1.63  Index Deletion       : 0.00
% 3.95/1.63  Index Matching       : 0.00
% 3.95/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
