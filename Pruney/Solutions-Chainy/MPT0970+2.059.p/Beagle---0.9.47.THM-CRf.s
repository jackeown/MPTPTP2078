%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:27 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  431 (6013 expanded)
%              Number of leaves         :   36 (2029 expanded)
%              Depth                    :   19
%              Number of atoms          :  776 (19071 expanded)
%              Number of equality atoms :  253 (6508 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_148,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_152,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_148])).

tff(c_52,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_153,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_52])).

tff(c_2461,plain,(
    ! [A_316,B_317,C_318] :
      ( m1_subset_1(k2_relset_1(A_316,B_317,C_318),k1_zfmisc_1(B_317))
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2478,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2461])).

tff(c_2484,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2478])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [C_56,A_57,B_58] :
      ( r2_hidden(C_56,A_57)
      | ~ r2_hidden(C_56,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_168,plain,(
    ! [A_79,B_80,A_81] :
      ( r2_hidden('#skF_1'(A_79,B_80),A_81)
      | ~ m1_subset_1(A_79,k1_zfmisc_1(A_81))
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_179,plain,(
    ! [A_79,A_81] :
      ( ~ m1_subset_1(A_79,k1_zfmisc_1(A_81))
      | r1_tarski(A_79,A_81) ) ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_2491,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2484,c_179])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2496,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2491,c_8])).

tff(c_2500,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_2496])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_197,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1(k2_relset_1(A_87,B_88,C_89),k1_zfmisc_1(B_88))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_214,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_197])).

tff(c_220,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_214])).

tff(c_227,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_220,c_179])).

tff(c_232,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_227,c_8])).

tff(c_236,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_232])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_158,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_162,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_158])).

tff(c_1893,plain,(
    ! [B_290,A_291,C_292] :
      ( k1_xboole_0 = B_290
      | k1_relset_1(A_291,B_290,C_292) = A_291
      | ~ v1_funct_2(C_292,A_291,B_290)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_291,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1900,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1893])).

tff(c_1904,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_1900])).

tff(c_1905,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1904])).

tff(c_62,plain,(
    ! [D_38] :
      ( r2_hidden('#skF_5'(D_38),'#skF_2')
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_106,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [D_38,B_54] :
      ( r2_hidden('#skF_5'(D_38),B_54)
      | ~ r1_tarski('#skF_2',B_54)
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_106])).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_99,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_102,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_99])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_102])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    ! [D_38] :
      ( k1_funct_1('#skF_4','#skF_5'(D_38)) = D_38
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_879,plain,(
    ! [A_179,C_180] :
      ( r2_hidden(k4_tarski(A_179,k1_funct_1(C_180,A_179)),C_180)
      | ~ r2_hidden(A_179,k1_relat_1(C_180))
      | ~ v1_funct_1(C_180)
      | ~ v1_relat_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_895,plain,(
    ! [D_38] :
      ( r2_hidden(k4_tarski('#skF_5'(D_38),D_38),'#skF_4')
      | ~ r2_hidden('#skF_5'(D_38),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_879])).

tff(c_904,plain,(
    ! [D_181] :
      ( r2_hidden(k4_tarski('#skF_5'(D_181),D_181),'#skF_4')
      | ~ r2_hidden('#skF_5'(D_181),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_181,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58,c_895])).

tff(c_20,plain,(
    ! [B_18,C_19,A_17] :
      ( r2_hidden(B_18,k2_relat_1(C_19))
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_910,plain,(
    ! [D_181] :
      ( r2_hidden(D_181,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden('#skF_5'(D_181),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_181,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_904,c_20])).

tff(c_929,plain,(
    ! [D_182] :
      ( r2_hidden(D_182,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_182),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_182,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_910])).

tff(c_939,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_112,c_929])).

tff(c_940,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_939])).

tff(c_1907,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_940])).

tff(c_1913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1907])).

tff(c_1914,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1904])).

tff(c_1570,plain,(
    ! [B_273,A_274,C_275] :
      ( k1_xboole_0 = B_273
      | k1_relset_1(A_274,B_273,C_275) = A_274
      | ~ v1_funct_2(C_275,A_274,B_273)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_274,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1577,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1570])).

tff(c_1581,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_1577])).

tff(c_1582,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1581])).

tff(c_1584,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_940])).

tff(c_1590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1584])).

tff(c_1591,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1581])).

tff(c_42,plain,(
    ! [C_34,A_32] :
      ( k1_xboole_0 = C_34
      | ~ v1_funct_2(C_34,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1702,plain,(
    ! [C_285,A_286] :
      ( C_285 = '#skF_3'
      | ~ v1_funct_2(C_285,A_286,'#skF_3')
      | A_286 = '#skF_3'
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_286,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1591,c_1591,c_1591,c_42])).

tff(c_1709,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_1702])).

tff(c_1713,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1709])).

tff(c_1714,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1713])).

tff(c_1592,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1581])).

tff(c_1718,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_1592])).

tff(c_1741,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_56])).

tff(c_1740,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_54])).

tff(c_48,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1603,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1('#skF_3',B_33,C_34) = '#skF_3'
      | ~ v1_funct_2(C_34,'#skF_3',B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_33))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1591,c_1591,c_1591,c_48])).

tff(c_1771,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1740,c_1603])).

tff(c_1796,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1771])).

tff(c_1735,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1714,c_162])).

tff(c_1826,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_1735])).

tff(c_1827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1718,c_1826])).

tff(c_1828,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1713])).

tff(c_184,plain,(
    ! [A_85,A_86] :
      ( ~ m1_subset_1(A_85,k1_zfmisc_1(A_86))
      | r1_tarski(A_85,A_86) ) ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_188,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_184])).

tff(c_1284,plain,(
    ! [B_242,A_243,C_244] :
      ( k1_xboole_0 = B_242
      | k1_relset_1(A_243,B_242,C_244) = A_243
      | ~ v1_funct_2(C_244,A_243,B_242)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_243,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1291,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1284])).

tff(c_1295,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_1291])).

tff(c_1296,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_1298,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_940])).

tff(c_1304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1298])).

tff(c_1305,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_1336,plain,(
    ! [C_246,A_247] :
      ( C_246 = '#skF_3'
      | ~ v1_funct_2(C_246,A_247,'#skF_3')
      | A_247 = '#skF_3'
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1305,c_1305,c_1305,c_42])).

tff(c_1343,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_1336])).

tff(c_1347,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1343])).

tff(c_1348,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1347])).

tff(c_1306,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_1349,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1306])).

tff(c_1375,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_56])).

tff(c_1369,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_162])).

tff(c_1374,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_54])).

tff(c_1311,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1('#skF_3',B_33,C_34) = '#skF_3'
      | ~ v1_funct_2(C_34,'#skF_3',B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_33))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1305,c_1305,c_1305,c_48])).

tff(c_1409,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1311])).

tff(c_1434,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1375,c_1369,c_1409])).

tff(c_1436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1349,c_1434])).

tff(c_1437,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1347])).

tff(c_417,plain,(
    ! [B_127,A_128,C_129] :
      ( k1_xboole_0 = B_127
      | k1_relset_1(A_128,B_127,C_129) = A_128
      | ~ v1_funct_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_424,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_417])).

tff(c_428,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_424])).

tff(c_429,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_365,plain,(
    ! [A_122,C_123] :
      ( r2_hidden(k4_tarski(A_122,k1_funct_1(C_123,A_122)),C_123)
      | ~ r2_hidden(A_122,k1_relat_1(C_123))
      | ~ v1_funct_1(C_123)
      | ~ v1_relat_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_390,plain,(
    ! [C_124,A_125] :
      ( r2_hidden(k1_funct_1(C_124,A_125),k2_relat_1(C_124))
      | ~ r2_hidden(A_125,k1_relat_1(C_124))
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_365,c_20])).

tff(c_397,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_38),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_390])).

tff(c_406,plain,(
    ! [D_126] :
      ( r2_hidden(D_126,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_126),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_126,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58,c_397])).

tff(c_416,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_112,c_406])).

tff(c_442,plain,(
    ! [D_130] :
      ( r2_hidden(D_130,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_130,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_429,c_416])).

tff(c_481,plain,(
    ! [A_133] :
      ( r1_tarski(A_133,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_133,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_442,c_4])).

tff(c_497,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_481])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_236,c_497])).

tff(c_505,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_545,plain,(
    ! [C_138,A_139] :
      ( C_138 = '#skF_3'
      | ~ v1_funct_2(C_138,A_139,'#skF_3')
      | A_139 = '#skF_3'
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_505,c_505,c_42])).

tff(c_552,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_545])).

tff(c_556,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_552])).

tff(c_557,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_506,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_585,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_506])).

tff(c_604,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_56])).

tff(c_598,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_162])).

tff(c_603,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_54])).

tff(c_707,plain,(
    ! [B_147,C_148] :
      ( k1_relset_1('#skF_3',B_147,C_148) = '#skF_3'
      | ~ v1_funct_2(C_148,'#skF_3',B_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_147))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_505,c_505,c_48])).

tff(c_710,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_603,c_707])).

tff(c_717,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_598,c_710])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_717])).

tff(c_720,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_16,plain,(
    ! [B_14,A_12] :
      ( v1_relat_1(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_228,plain,
    ( v1_relat_1(k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_220,c_16])).

tff(c_237,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_736,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_237])).

tff(c_754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_736])).

tff(c_756,plain,(
    v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_1106,plain,(
    ! [B_213,A_214,C_215] :
      ( k1_xboole_0 = B_213
      | k1_relset_1(A_214,B_213,C_215) = A_214
      | ~ v1_funct_2(C_215,A_214,B_213)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_214,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1113,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1106])).

tff(c_1117,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_1113])).

tff(c_1118,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1117])).

tff(c_1120,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1118,c_940])).

tff(c_1126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1120])).

tff(c_1127,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1117])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_948,plain,(
    ! [C_185,A_186] :
      ( r2_hidden(k1_funct_1(C_185,A_186),k2_relat_1(C_185))
      | ~ r2_hidden(A_186,k1_relat_1(C_185))
      | ~ v1_funct_1(C_185)
      | ~ v1_relat_1(C_185) ) ),
    inference(resolution,[status(thm)],[c_879,c_20])).

tff(c_958,plain,(
    ! [A_186] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_186),k1_xboole_0)
      | ~ r2_hidden(A_186,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_948])).

tff(c_963,plain,(
    ! [A_186] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_186),k1_xboole_0)
      | ~ r2_hidden(A_186,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_958])).

tff(c_964,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_1131,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_964])).

tff(c_1140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_1131])).

tff(c_1141,plain,(
    ! [A_186] :
      ( ~ v1_funct_1(k1_xboole_0)
      | r2_hidden(k1_funct_1(k1_xboole_0,A_186),k1_xboole_0)
      | ~ r2_hidden(A_186,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_1153,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_1309,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1153])).

tff(c_1443,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1309])).

tff(c_1480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1443])).

tff(c_1483,plain,(
    ! [A_250] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_250),k1_xboole_0)
      | ~ r2_hidden(A_250,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1490,plain,(
    ! [A_251,B_252] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_251),B_252)
      | ~ r1_tarski(k1_xboole_0,B_252)
      | ~ r2_hidden(A_251,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1483,c_2])).

tff(c_1515,plain,(
    ! [A_258,B_259,B_260] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_258),B_259)
      | ~ r1_tarski(B_260,B_259)
      | ~ r1_tarski(k1_xboole_0,B_260)
      | ~ r2_hidden(A_258,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1490,c_2])).

tff(c_1526,plain,(
    ! [A_258] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_258),k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(k1_xboole_0,'#skF_4')
      | ~ r2_hidden(A_258,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_188,c_1515])).

tff(c_1529,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1526])).

tff(c_1594,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1529])).

tff(c_1837,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_1594])).

tff(c_1872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1837])).

tff(c_1874,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1526])).

tff(c_1918,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_1874])).

tff(c_120,plain,(
    ! [D_59,B_60] :
      ( r2_hidden('#skF_5'(D_59),B_60)
      | ~ r1_tarski('#skF_2',B_60)
      | ~ r2_hidden(D_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_106])).

tff(c_126,plain,(
    ! [D_59,B_2,B_60] :
      ( r2_hidden('#skF_5'(D_59),B_2)
      | ~ r1_tarski(B_60,B_2)
      | ~ r1_tarski('#skF_2',B_60)
      | ~ r2_hidden(D_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_193,plain,(
    ! [D_59] :
      ( r2_hidden('#skF_5'(D_59),k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_2','#skF_4')
      | ~ r2_hidden(D_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_188,c_126])).

tff(c_196,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_2106,plain,(
    ! [C_301,A_302] :
      ( C_301 = '#skF_3'
      | ~ v1_funct_2(C_301,A_302,'#skF_3')
      | A_302 = '#skF_3'
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_302,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_1914,c_1914,c_1914,c_42])).

tff(c_2113,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_2106])).

tff(c_2117,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2113])).

tff(c_2118,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2117])).

tff(c_1990,plain,(
    ! [C_297,A_298] :
      ( C_297 = '#skF_3'
      | ~ v1_funct_2(C_297,A_298,'#skF_3')
      | A_298 = '#skF_3'
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_298,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_1914,c_1914,c_1914,c_42])).

tff(c_1997,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_1990])).

tff(c_2001,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1997])).

tff(c_2002,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2001])).

tff(c_1961,plain,(
    ! [D_59] :
      ( r2_hidden('#skF_5'(D_59),'#skF_4')
      | ~ r1_tarski('#skF_2','#skF_3')
      | ~ r2_hidden(D_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1918,c_126])).

tff(c_1988,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1961])).

tff(c_2003,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2002,c_1988])).

tff(c_2030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2003])).

tff(c_2031,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2001])).

tff(c_1891,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1874,c_8])).

tff(c_1892,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1891])).

tff(c_1916,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_1892])).

tff(c_2039,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_1916])).

tff(c_2074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2039])).

tff(c_2076,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1961])).

tff(c_2090,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2076,c_8])).

tff(c_2091,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2090])).

tff(c_2119,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_2091])).

tff(c_2147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2119])).

tff(c_2148,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2117])).

tff(c_2155,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2148,c_2076])).

tff(c_2193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_2155])).

tff(c_2194,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2090])).

tff(c_2210,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2194,c_196])).

tff(c_2224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_2210])).

tff(c_2225,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1891])).

tff(c_2241,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2225,c_2225,c_26])).

tff(c_2240,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2225,c_2225,c_24])).

tff(c_2259,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2240,c_153])).

tff(c_50,plain,(
    ! [B_33,A_32,C_34] :
      ( k1_xboole_0 = B_33
      | k1_relset_1(A_32,B_33,C_34) = A_32
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2272,plain,(
    ! [B_303,A_304,C_305] :
      ( B_303 = '#skF_4'
      | k1_relset_1(A_304,B_303,C_305) = A_304
      | ~ v1_funct_2(C_305,A_304,B_303)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_304,B_303))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2225,c_50])).

tff(c_2279,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2272])).

tff(c_2283,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_2279])).

tff(c_2284,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2259,c_2283])).

tff(c_2316,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_2284])).

tff(c_2325,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2316,c_196])).

tff(c_2336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2325])).

tff(c_2353,plain,(
    ! [D_306] :
      ( r2_hidden(D_306,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_306,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_939])).

tff(c_2419,plain,(
    ! [A_314] :
      ( r1_tarski(A_314,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_314,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2353,c_4])).

tff(c_2435,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_2419])).

tff(c_2442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_236,c_2435])).

tff(c_2444,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_4675,plain,(
    ! [B_547,A_548,C_549] :
      ( k1_xboole_0 = B_547
      | k1_relset_1(A_548,B_547,C_549) = A_548
      | ~ v1_funct_2(C_549,A_548,B_547)
      | ~ m1_subset_1(C_549,k1_zfmisc_1(k2_zfmisc_1(A_548,B_547))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4682,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_4675])).

tff(c_4686,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_4682])).

tff(c_4707,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4686])).

tff(c_3482,plain,(
    ! [A_455,C_456] :
      ( r2_hidden(k4_tarski(A_455,k1_funct_1(C_456,A_455)),C_456)
      | ~ r2_hidden(A_455,k1_relat_1(C_456))
      | ~ v1_funct_1(C_456)
      | ~ v1_relat_1(C_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3498,plain,(
    ! [D_38] :
      ( r2_hidden(k4_tarski('#skF_5'(D_38),D_38),'#skF_4')
      | ~ r2_hidden('#skF_5'(D_38),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3482])).

tff(c_3550,plain,(
    ! [D_459] :
      ( r2_hidden(k4_tarski('#skF_5'(D_459),D_459),'#skF_4')
      | ~ r2_hidden('#skF_5'(D_459),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_459,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58,c_3498])).

tff(c_3556,plain,(
    ! [D_459] :
      ( r2_hidden(D_459,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden('#skF_5'(D_459),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_459,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3550,c_20])).

tff(c_3575,plain,(
    ! [D_460] :
      ( r2_hidden(D_460,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_460),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_460,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_3556])).

tff(c_3600,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_112,c_3575])).

tff(c_3601,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3600])).

tff(c_4713,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4707,c_3601])).

tff(c_4719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4713])).

tff(c_4720,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4686])).

tff(c_4824,plain,(
    ! [C_554,A_555] :
      ( C_554 = '#skF_3'
      | ~ v1_funct_2(C_554,A_555,'#skF_3')
      | A_555 = '#skF_3'
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_555,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4720,c_4720,c_4720,c_4720,c_42])).

tff(c_4831,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_4824])).

tff(c_4835,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4831])).

tff(c_4836,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4835])).

tff(c_4148,plain,(
    ! [B_521,A_522,C_523] :
      ( k1_xboole_0 = B_521
      | k1_relset_1(A_522,B_521,C_523) = A_522
      | ~ v1_funct_2(C_523,A_522,B_521)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_522,B_521))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4155,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_4148])).

tff(c_4159,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_4155])).

tff(c_4160,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4159])).

tff(c_4166,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4160,c_3601])).

tff(c_4172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4166])).

tff(c_4173,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4159])).

tff(c_4447,plain,(
    ! [C_543,A_544] :
      ( C_543 = '#skF_3'
      | ~ v1_funct_2(C_543,A_544,'#skF_3')
      | A_544 = '#skF_3'
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_544,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4173,c_4173,c_4173,c_42])).

tff(c_4454,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_4447])).

tff(c_4458,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4454])).

tff(c_4459,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4458])).

tff(c_3837,plain,(
    ! [B_500,A_501,C_502] :
      ( k1_xboole_0 = B_500
      | k1_relset_1(A_501,B_500,C_502) = A_501
      | ~ v1_funct_2(C_502,A_501,B_500)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_501,B_500))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3844,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_3837])).

tff(c_3848,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_3844])).

tff(c_3849,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3848])).

tff(c_3855,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3849,c_3601])).

tff(c_3861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3855])).

tff(c_3862,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3848])).

tff(c_3894,plain,(
    ! [C_504,A_505] :
      ( C_504 = '#skF_3'
      | ~ v1_funct_2(C_504,A_505,'#skF_3')
      | A_505 = '#skF_3'
      | ~ m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(A_505,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3862,c_3862,c_3862,c_42])).

tff(c_3901,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_3894])).

tff(c_3905,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3901])).

tff(c_3906,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3905])).

tff(c_3863,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3848])).

tff(c_3907,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_3863])).

tff(c_3941,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_56])).

tff(c_3935,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_162])).

tff(c_3940,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_54])).

tff(c_4039,plain,(
    ! [B_508,C_509] :
      ( k1_relset_1('#skF_3',B_508,C_509) = '#skF_3'
      | ~ v1_funct_2(C_509,'#skF_3',B_508)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_508))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3862,c_3862,c_3862,c_48])).

tff(c_4042,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3940,c_4039])).

tff(c_4049,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3941,c_3935,c_4042])).

tff(c_4051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3907,c_4049])).

tff(c_4052,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3905])).

tff(c_2906,plain,(
    ! [B_388,A_389,C_390] :
      ( k1_xboole_0 = B_388
      | k1_relset_1(A_389,B_388,C_390) = A_389
      | ~ v1_funct_2(C_390,A_389,B_388)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_389,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2913,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2906])).

tff(c_2917,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_2913])).

tff(c_2918,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2917])).

tff(c_2643,plain,(
    ! [A_358,C_359] :
      ( r2_hidden(k4_tarski(A_358,k1_funct_1(C_359,A_358)),C_359)
      | ~ r2_hidden(A_358,k1_relat_1(C_359))
      | ~ v1_funct_1(C_359)
      | ~ v1_relat_1(C_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2659,plain,(
    ! [D_38] :
      ( r2_hidden(k4_tarski('#skF_5'(D_38),D_38),'#skF_4')
      | ~ r2_hidden('#skF_5'(D_38),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2643])).

tff(c_2699,plain,(
    ! [D_365] :
      ( r2_hidden(k4_tarski('#skF_5'(D_365),D_365),'#skF_4')
      | ~ r2_hidden('#skF_5'(D_365),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_365,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58,c_2659])).

tff(c_2705,plain,(
    ! [D_365] :
      ( r2_hidden(D_365,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden('#skF_5'(D_365),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_365,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2699,c_20])).

tff(c_2740,plain,(
    ! [D_367] :
      ( r2_hidden(D_367,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_367),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_367,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2705])).

tff(c_2765,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_112,c_2740])).

tff(c_2766,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2765])).

tff(c_2924,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2918,c_2766])).

tff(c_2930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2924])).

tff(c_2931,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2917])).

tff(c_2976,plain,(
    ! [C_393,A_394] :
      ( C_393 = '#skF_3'
      | ~ v1_funct_2(C_393,A_394,'#skF_3')
      | A_394 = '#skF_3'
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_394,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2931,c_2931,c_2931,c_2931,c_42])).

tff(c_2983,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_2976])).

tff(c_2987,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2983])).

tff(c_3000,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2987])).

tff(c_2932,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2917])).

tff(c_3002,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3000,c_2932])).

tff(c_3035,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3000,c_56])).

tff(c_3034,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3000,c_54])).

tff(c_2936,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1('#skF_3',B_33,C_34) = '#skF_3'
      | ~ v1_funct_2(C_34,'#skF_3',B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_33))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2931,c_2931,c_2931,c_2931,c_48])).

tff(c_3068,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3034,c_2936])).

tff(c_3094,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3035,c_3068])).

tff(c_3029,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3000,c_162])).

tff(c_3124,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_3029])).

tff(c_3125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3002,c_3124])).

tff(c_3126,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2987])).

tff(c_2492,plain,
    ( v1_relat_1(k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2484,c_16])).

tff(c_2513,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2492])).

tff(c_3155,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3126,c_2513])).

tff(c_3175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_3155])).

tff(c_3201,plain,(
    ! [D_402] :
      ( r2_hidden(D_402,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_402,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_2765])).

tff(c_3236,plain,(
    ! [A_404] :
      ( r1_tarski(A_404,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_404,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3201,c_4])).

tff(c_3252,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_3236])).

tff(c_3259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2500,c_2500,c_3252])).

tff(c_3261,plain,(
    v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2492])).

tff(c_3745,plain,(
    ! [B_489,A_490,C_491] :
      ( k1_xboole_0 = B_489
      | k1_relset_1(A_490,B_489,C_491) = A_490
      | ~ v1_funct_2(C_491,A_490,B_489)
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(A_490,B_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3752,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_3745])).

tff(c_3756,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_162,c_3752])).

tff(c_3757,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3756])).

tff(c_3763,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3757,c_3601])).

tff(c_3769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3763])).

tff(c_3770,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3756])).

tff(c_3637,plain,(
    ! [C_468,A_469] :
      ( r2_hidden(k1_funct_1(C_468,A_469),k2_relat_1(C_468))
      | ~ r2_hidden(A_469,k1_relat_1(C_468))
      | ~ v1_funct_1(C_468)
      | ~ v1_relat_1(C_468) ) ),
    inference(resolution,[status(thm)],[c_3482,c_20])).

tff(c_3647,plain,(
    ! [A_469] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_469),k1_xboole_0)
      | ~ r2_hidden(A_469,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3637])).

tff(c_3652,plain,(
    ! [A_469] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_469),k1_xboole_0)
      | ~ r2_hidden(A_469,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3647])).

tff(c_3664,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3652])).

tff(c_3773,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3770,c_3664])).

tff(c_3783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3261,c_3773])).

tff(c_3784,plain,(
    ! [A_469] :
      ( ~ v1_funct_1(k1_xboole_0)
      | r2_hidden(k1_funct_1(k1_xboole_0,A_469),k1_xboole_0)
      | ~ r2_hidden(A_469,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_3652])).

tff(c_3805,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3784])).

tff(c_3865,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3805])).

tff(c_4058,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4052,c_3865])).

tff(c_4103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4058])).

tff(c_4106,plain,(
    ! [A_510] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_510),k1_xboole_0)
      | ~ r2_hidden(A_510,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_3784])).

tff(c_4114,plain,(
    ! [A_514,B_515] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_514),B_515)
      | ~ r1_tarski(k1_xboole_0,B_515)
      | ~ r2_hidden(A_514,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4106,c_2])).

tff(c_4128,plain,(
    ! [A_518,B_519,B_520] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_518),B_519)
      | ~ r1_tarski(B_520,B_519)
      | ~ r1_tarski(k1_xboole_0,B_520)
      | ~ r2_hidden(A_518,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4114,c_2])).

tff(c_4144,plain,(
    ! [A_518] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_518),'#skF_4')
      | ~ r1_tarski(k1_xboole_0,'#skF_2')
      | ~ r2_hidden(A_518,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2444,c_4128])).

tff(c_4147,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4144])).

tff(c_4176,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4147])).

tff(c_4461,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_4176])).

tff(c_4500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4461])).

tff(c_4501,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4458])).

tff(c_4252,plain,(
    ! [C_532,A_533] :
      ( C_532 = '#skF_3'
      | ~ v1_funct_2(C_532,A_533,'#skF_3')
      | A_533 = '#skF_3'
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_533,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4173,c_4173,c_4173,c_42])).

tff(c_4259,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_4252])).

tff(c_4263,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4259])).

tff(c_4264,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4263])).

tff(c_4265,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4264,c_4176])).

tff(c_4304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4265])).

tff(c_4305,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4263])).

tff(c_4145,plain,(
    ! [A_518] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_518),k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(k1_xboole_0,'#skF_4')
      | ~ r2_hidden(A_518,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_188,c_4128])).

tff(c_4195,plain,(
    ! [A_518] :
      ( r2_hidden(k1_funct_1('#skF_3',A_518),k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_3','#skF_4')
      | ~ r2_hidden(A_518,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4173,c_4173,c_4145])).

tff(c_4196,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4195])).

tff(c_4314,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4305,c_4196])).

tff(c_4361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4314])).

tff(c_4363,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_4195])).

tff(c_4391,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4363,c_8])).

tff(c_4393,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4391])).

tff(c_4509,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4501,c_4393])).

tff(c_4559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4509])).

tff(c_4560,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4391])).

tff(c_4189,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4173,c_4173,c_26])).

tff(c_4585,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4560,c_4560,c_4189])).

tff(c_2446,plain,(
    ! [D_59] :
      ( r2_hidden('#skF_5'(D_59),'#skF_4')
      | ~ r1_tarski('#skF_2','#skF_2')
      | ~ r2_hidden(D_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2444,c_126])).

tff(c_2454,plain,(
    ! [D_315] :
      ( r2_hidden('#skF_5'(D_315),'#skF_4')
      | ~ r2_hidden(D_315,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2446])).

tff(c_2460,plain,(
    ! [D_315,B_2] :
      ( r2_hidden('#skF_5'(D_315),B_2)
      | ~ r1_tarski('#skF_4',B_2)
      | ~ r2_hidden(D_315,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2454,c_2])).

tff(c_3598,plain,(
    ! [D_315] :
      ( r2_hidden(D_315,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_4',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_315,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2460,c_3575])).

tff(c_3602,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3598])).

tff(c_4644,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4585,c_3602])).

tff(c_4648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4644])).

tff(c_4650,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4144])).

tff(c_4674,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4650,c_8])).

tff(c_4821,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4720,c_4720,c_4674])).

tff(c_4822,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4821])).

tff(c_4837,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4836,c_4822])).

tff(c_4877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4837])).

tff(c_4878,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4835])).

tff(c_136,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_3360,plain,(
    ! [A_434,B_435,B_436,B_437] :
      ( r2_hidden('#skF_1'(A_434,B_435),B_436)
      | ~ r1_tarski(B_437,B_436)
      | ~ r1_tarski(A_434,B_437)
      | r1_tarski(A_434,B_435) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_3379,plain,(
    ! [A_440,B_441] :
      ( r2_hidden('#skF_1'(A_440,B_441),'#skF_4')
      | ~ r1_tarski(A_440,'#skF_2')
      | r1_tarski(A_440,B_441) ) ),
    inference(resolution,[status(thm)],[c_2444,c_3360])).

tff(c_3390,plain,(
    ! [A_440] :
      ( ~ r1_tarski(A_440,'#skF_2')
      | r1_tarski(A_440,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3379,c_4])).

tff(c_4669,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4650,c_3390])).

tff(c_4732,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4720,c_4669])).

tff(c_4800,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4732,c_8])).

tff(c_4823,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4800])).

tff(c_4882,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4878,c_4823])).

tff(c_4934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4882])).

tff(c_4935,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4800])).

tff(c_4937,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4935,c_4822])).

tff(c_4988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_4937])).

tff(c_4989,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4821])).

tff(c_4721,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4686])).

tff(c_4992,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4989,c_4721])).

tff(c_5027,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4989,c_56])).

tff(c_5021,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4989,c_162])).

tff(c_5026,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4989,c_54])).

tff(c_5144,plain,(
    ! [B_562,C_563] :
      ( k1_relset_1('#skF_3',B_562,C_563) = '#skF_3'
      | ~ v1_funct_2(C_563,'#skF_3',B_562)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_562))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4720,c_4720,c_4720,c_4720,c_48])).

tff(c_5147,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_5026,c_5144])).

tff(c_5154,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5027,c_5021,c_5147])).

tff(c_5156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4992,c_5154])).

tff(c_5158,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3598])).

tff(c_3456,plain,(
    ! [A_450,B_451,B_452] :
      ( r2_hidden('#skF_1'(A_450,B_451),B_452)
      | ~ r1_tarski('#skF_4',B_452)
      | ~ r1_tarski(A_450,'#skF_2')
      | r1_tarski(A_450,B_451) ) ),
    inference(resolution,[status(thm)],[c_3379,c_2])).

tff(c_3467,plain,(
    ! [B_452,A_450] :
      ( ~ r1_tarski('#skF_4',B_452)
      | ~ r1_tarski(A_450,'#skF_2')
      | r1_tarski(A_450,B_452) ) ),
    inference(resolution,[status(thm)],[c_3456,c_4])).

tff(c_5214,plain,(
    ! [A_565] :
      ( ~ r1_tarski(A_565,'#skF_2')
      | r1_tarski(A_565,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5158,c_3467])).

tff(c_5217,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_5214,c_3601])).

tff(c_5242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5217])).

tff(c_5263,plain,(
    ! [D_566] :
      ( r2_hidden(D_566,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_566,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_3600])).

tff(c_5333,plain,(
    ! [A_574] :
      ( r1_tarski(A_574,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_574,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5263,c_4])).

tff(c_5353,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_5333])).

tff(c_5361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2500,c_2500,c_5353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.57/2.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.54  
% 6.94/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.54  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.94/2.54  
% 6.94/2.54  %Foreground sorts:
% 6.94/2.54  
% 6.94/2.54  
% 6.94/2.54  %Background operators:
% 6.94/2.54  
% 6.94/2.54  
% 6.94/2.54  %Foreground operators:
% 6.94/2.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.94/2.54  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.94/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.94/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.94/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.94/2.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.94/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.94/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.94/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.94/2.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.94/2.54  tff('#skF_2', type, '#skF_2': $i).
% 6.94/2.54  tff('#skF_3', type, '#skF_3': $i).
% 6.94/2.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.94/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.94/2.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.94/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.94/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.94/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.94/2.54  tff('#skF_4', type, '#skF_4': $i).
% 6.94/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.94/2.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.94/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.94/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.94/2.54  
% 6.94/2.59  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 6.94/2.59  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.94/2.59  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.94/2.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.94/2.59  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.94/2.59  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.94/2.59  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.94/2.59  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.94/2.59  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.94/2.59  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.94/2.59  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 6.94/2.59  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 6.94/2.59  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.94/2.59  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.94/2.59  tff(c_148, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.94/2.59  tff(c_152, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_148])).
% 6.94/2.59  tff(c_52, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.94/2.59  tff(c_153, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_52])).
% 6.94/2.59  tff(c_2461, plain, (![A_316, B_317, C_318]: (m1_subset_1(k2_relset_1(A_316, B_317, C_318), k1_zfmisc_1(B_317)) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.94/2.59  tff(c_2478, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_152, c_2461])).
% 6.94/2.59  tff(c_2484, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2478])).
% 6.94/2.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.59  tff(c_113, plain, (![C_56, A_57, B_58]: (r2_hidden(C_56, A_57) | ~r2_hidden(C_56, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.94/2.59  tff(c_168, plain, (![A_79, B_80, A_81]: (r2_hidden('#skF_1'(A_79, B_80), A_81) | ~m1_subset_1(A_79, k1_zfmisc_1(A_81)) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_6, c_113])).
% 6.94/2.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.59  tff(c_179, plain, (![A_79, A_81]: (~m1_subset_1(A_79, k1_zfmisc_1(A_81)) | r1_tarski(A_79, A_81))), inference(resolution, [status(thm)], [c_168, c_4])).
% 6.94/2.59  tff(c_2491, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2484, c_179])).
% 6.94/2.59  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.94/2.59  tff(c_2496, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2491, c_8])).
% 6.94/2.59  tff(c_2500, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_153, c_2496])).
% 6.94/2.59  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.94/2.59  tff(c_197, plain, (![A_87, B_88, C_89]: (m1_subset_1(k2_relset_1(A_87, B_88, C_89), k1_zfmisc_1(B_88)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.94/2.59  tff(c_214, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_152, c_197])).
% 6.94/2.59  tff(c_220, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_214])).
% 6.94/2.59  tff(c_227, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_220, c_179])).
% 6.94/2.59  tff(c_232, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_227, c_8])).
% 6.94/2.59  tff(c_236, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_153, c_232])).
% 6.94/2.59  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.94/2.59  tff(c_158, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.94/2.59  tff(c_162, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_158])).
% 6.94/2.59  tff(c_1893, plain, (![B_290, A_291, C_292]: (k1_xboole_0=B_290 | k1_relset_1(A_291, B_290, C_292)=A_291 | ~v1_funct_2(C_292, A_291, B_290) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_291, B_290))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_1900, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1893])).
% 6.94/2.59  tff(c_1904, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_1900])).
% 6.94/2.59  tff(c_1905, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1904])).
% 6.94/2.59  tff(c_62, plain, (![D_38]: (r2_hidden('#skF_5'(D_38), '#skF_2') | ~r2_hidden(D_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.94/2.59  tff(c_106, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.59  tff(c_112, plain, (![D_38, B_54]: (r2_hidden('#skF_5'(D_38), B_54) | ~r1_tarski('#skF_2', B_54) | ~r2_hidden(D_38, '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_106])).
% 6.94/2.59  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.94/2.59  tff(c_99, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.94/2.59  tff(c_102, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_99])).
% 6.94/2.59  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_102])).
% 6.94/2.59  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.94/2.59  tff(c_60, plain, (![D_38]: (k1_funct_1('#skF_4', '#skF_5'(D_38))=D_38 | ~r2_hidden(D_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.94/2.59  tff(c_879, plain, (![A_179, C_180]: (r2_hidden(k4_tarski(A_179, k1_funct_1(C_180, A_179)), C_180) | ~r2_hidden(A_179, k1_relat_1(C_180)) | ~v1_funct_1(C_180) | ~v1_relat_1(C_180))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.94/2.59  tff(c_895, plain, (![D_38]: (r2_hidden(k4_tarski('#skF_5'(D_38), D_38), '#skF_4') | ~r2_hidden('#skF_5'(D_38), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_38, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_879])).
% 6.94/2.59  tff(c_904, plain, (![D_181]: (r2_hidden(k4_tarski('#skF_5'(D_181), D_181), '#skF_4') | ~r2_hidden('#skF_5'(D_181), k1_relat_1('#skF_4')) | ~r2_hidden(D_181, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58, c_895])).
% 6.94/2.59  tff(c_20, plain, (![B_18, C_19, A_17]: (r2_hidden(B_18, k2_relat_1(C_19)) | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.94/2.59  tff(c_910, plain, (![D_181]: (r2_hidden(D_181, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~r2_hidden('#skF_5'(D_181), k1_relat_1('#skF_4')) | ~r2_hidden(D_181, '#skF_3'))), inference(resolution, [status(thm)], [c_904, c_20])).
% 6.94/2.59  tff(c_929, plain, (![D_182]: (r2_hidden(D_182, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_182), k1_relat_1('#skF_4')) | ~r2_hidden(D_182, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_910])).
% 6.94/2.59  tff(c_939, plain, (![D_38]: (r2_hidden(D_38, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_38, '#skF_3'))), inference(resolution, [status(thm)], [c_112, c_929])).
% 6.94/2.59  tff(c_940, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_939])).
% 6.94/2.59  tff(c_1907, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1905, c_940])).
% 6.94/2.59  tff(c_1913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1907])).
% 6.94/2.59  tff(c_1914, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1904])).
% 6.94/2.59  tff(c_1570, plain, (![B_273, A_274, C_275]: (k1_xboole_0=B_273 | k1_relset_1(A_274, B_273, C_275)=A_274 | ~v1_funct_2(C_275, A_274, B_273) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_274, B_273))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_1577, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1570])).
% 6.94/2.59  tff(c_1581, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_1577])).
% 6.94/2.59  tff(c_1582, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1581])).
% 6.94/2.59  tff(c_1584, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_940])).
% 6.94/2.59  tff(c_1590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1584])).
% 6.94/2.59  tff(c_1591, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1581])).
% 6.94/2.59  tff(c_42, plain, (![C_34, A_32]: (k1_xboole_0=C_34 | ~v1_funct_2(C_34, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_1702, plain, (![C_285, A_286]: (C_285='#skF_3' | ~v1_funct_2(C_285, A_286, '#skF_3') | A_286='#skF_3' | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_286, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1591, c_1591, c_1591, c_42])).
% 6.94/2.59  tff(c_1709, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_1702])).
% 6.94/2.59  tff(c_1713, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1709])).
% 6.94/2.59  tff(c_1714, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1713])).
% 6.94/2.59  tff(c_1592, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_1581])).
% 6.94/2.59  tff(c_1718, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_1592])).
% 6.94/2.59  tff(c_1741, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_56])).
% 6.94/2.59  tff(c_1740, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_54])).
% 6.94/2.59  tff(c_48, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_1603, plain, (![B_33, C_34]: (k1_relset_1('#skF_3', B_33, C_34)='#skF_3' | ~v1_funct_2(C_34, '#skF_3', B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_33))))), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1591, c_1591, c_1591, c_48])).
% 6.94/2.59  tff(c_1771, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1740, c_1603])).
% 6.94/2.59  tff(c_1796, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1771])).
% 6.94/2.59  tff(c_1735, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1714, c_162])).
% 6.94/2.59  tff(c_1826, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_1735])).
% 6.94/2.59  tff(c_1827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1718, c_1826])).
% 6.94/2.59  tff(c_1828, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1713])).
% 6.94/2.59  tff(c_184, plain, (![A_85, A_86]: (~m1_subset_1(A_85, k1_zfmisc_1(A_86)) | r1_tarski(A_85, A_86))), inference(resolution, [status(thm)], [c_168, c_4])).
% 6.94/2.59  tff(c_188, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_184])).
% 6.94/2.59  tff(c_1284, plain, (![B_242, A_243, C_244]: (k1_xboole_0=B_242 | k1_relset_1(A_243, B_242, C_244)=A_243 | ~v1_funct_2(C_244, A_243, B_242) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_1291, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1284])).
% 6.94/2.59  tff(c_1295, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_1291])).
% 6.94/2.59  tff(c_1296, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1295])).
% 6.94/2.59  tff(c_1298, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_940])).
% 6.94/2.59  tff(c_1304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1298])).
% 6.94/2.59  tff(c_1305, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1295])).
% 6.94/2.59  tff(c_1336, plain, (![C_246, A_247]: (C_246='#skF_3' | ~v1_funct_2(C_246, A_247, '#skF_3') | A_247='#skF_3' | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1305, c_1305, c_1305, c_42])).
% 6.94/2.59  tff(c_1343, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_1336])).
% 6.94/2.59  tff(c_1347, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1343])).
% 6.94/2.59  tff(c_1348, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1347])).
% 6.94/2.59  tff(c_1306, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_1295])).
% 6.94/2.59  tff(c_1349, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1306])).
% 6.94/2.59  tff(c_1375, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_56])).
% 6.94/2.59  tff(c_1369, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_162])).
% 6.94/2.59  tff(c_1374, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_54])).
% 6.94/2.59  tff(c_1311, plain, (![B_33, C_34]: (k1_relset_1('#skF_3', B_33, C_34)='#skF_3' | ~v1_funct_2(C_34, '#skF_3', B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_33))))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1305, c_1305, c_1305, c_48])).
% 6.94/2.59  tff(c_1409, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1311])).
% 6.94/2.59  tff(c_1434, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1375, c_1369, c_1409])).
% 6.94/2.59  tff(c_1436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1349, c_1434])).
% 6.94/2.59  tff(c_1437, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1347])).
% 6.94/2.59  tff(c_417, plain, (![B_127, A_128, C_129]: (k1_xboole_0=B_127 | k1_relset_1(A_128, B_127, C_129)=A_128 | ~v1_funct_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_424, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_417])).
% 6.94/2.59  tff(c_428, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_424])).
% 6.94/2.59  tff(c_429, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_428])).
% 6.94/2.59  tff(c_365, plain, (![A_122, C_123]: (r2_hidden(k4_tarski(A_122, k1_funct_1(C_123, A_122)), C_123) | ~r2_hidden(A_122, k1_relat_1(C_123)) | ~v1_funct_1(C_123) | ~v1_relat_1(C_123))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.94/2.59  tff(c_390, plain, (![C_124, A_125]: (r2_hidden(k1_funct_1(C_124, A_125), k2_relat_1(C_124)) | ~r2_hidden(A_125, k1_relat_1(C_124)) | ~v1_funct_1(C_124) | ~v1_relat_1(C_124))), inference(resolution, [status(thm)], [c_365, c_20])).
% 6.94/2.59  tff(c_397, plain, (![D_38]: (r2_hidden(D_38, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_38), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_38, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_390])).
% 6.94/2.59  tff(c_406, plain, (![D_126]: (r2_hidden(D_126, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_126), k1_relat_1('#skF_4')) | ~r2_hidden(D_126, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58, c_397])).
% 6.94/2.59  tff(c_416, plain, (![D_38]: (r2_hidden(D_38, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_38, '#skF_3'))), inference(resolution, [status(thm)], [c_112, c_406])).
% 6.94/2.59  tff(c_442, plain, (![D_130]: (r2_hidden(D_130, k2_relat_1('#skF_4')) | ~r2_hidden(D_130, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_429, c_416])).
% 6.94/2.59  tff(c_481, plain, (![A_133]: (r1_tarski(A_133, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_133, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_442, c_4])).
% 6.94/2.59  tff(c_497, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_481])).
% 6.94/2.59  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_236, c_497])).
% 6.94/2.59  tff(c_505, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_428])).
% 6.94/2.59  tff(c_545, plain, (![C_138, A_139]: (C_138='#skF_3' | ~v1_funct_2(C_138, A_139, '#skF_3') | A_139='#skF_3' | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_505, c_505, c_42])).
% 6.94/2.59  tff(c_552, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_545])).
% 6.94/2.59  tff(c_556, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_552])).
% 6.94/2.59  tff(c_557, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_556])).
% 6.94/2.59  tff(c_506, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_428])).
% 6.94/2.59  tff(c_585, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_557, c_506])).
% 6.94/2.59  tff(c_604, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_56])).
% 6.94/2.59  tff(c_598, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_162])).
% 6.94/2.59  tff(c_603, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_54])).
% 6.94/2.59  tff(c_707, plain, (![B_147, C_148]: (k1_relset_1('#skF_3', B_147, C_148)='#skF_3' | ~v1_funct_2(C_148, '#skF_3', B_147) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_147))))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_505, c_505, c_48])).
% 6.94/2.59  tff(c_710, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_603, c_707])).
% 6.94/2.59  tff(c_717, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_604, c_598, c_710])).
% 6.94/2.59  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_585, c_717])).
% 6.94/2.59  tff(c_720, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_556])).
% 6.94/2.59  tff(c_16, plain, (![B_14, A_12]: (v1_relat_1(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.94/2.59  tff(c_228, plain, (v1_relat_1(k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_220, c_16])).
% 6.94/2.59  tff(c_237, plain, (~v1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_228])).
% 6.94/2.59  tff(c_736, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_720, c_237])).
% 6.94/2.59  tff(c_754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_736])).
% 6.94/2.59  tff(c_756, plain, (v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_228])).
% 6.94/2.59  tff(c_1106, plain, (![B_213, A_214, C_215]: (k1_xboole_0=B_213 | k1_relset_1(A_214, B_213, C_215)=A_214 | ~v1_funct_2(C_215, A_214, B_213) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_214, B_213))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_1113, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1106])).
% 6.94/2.59  tff(c_1117, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_1113])).
% 6.94/2.59  tff(c_1118, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1117])).
% 6.94/2.59  tff(c_1120, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1118, c_940])).
% 6.94/2.59  tff(c_1126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1120])).
% 6.94/2.59  tff(c_1127, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1117])).
% 6.94/2.59  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.94/2.59  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.94/2.59  tff(c_948, plain, (![C_185, A_186]: (r2_hidden(k1_funct_1(C_185, A_186), k2_relat_1(C_185)) | ~r2_hidden(A_186, k1_relat_1(C_185)) | ~v1_funct_1(C_185) | ~v1_relat_1(C_185))), inference(resolution, [status(thm)], [c_879, c_20])).
% 6.94/2.59  tff(c_958, plain, (![A_186]: (r2_hidden(k1_funct_1(k1_xboole_0, A_186), k1_xboole_0) | ~r2_hidden(A_186, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_948])).
% 6.94/2.59  tff(c_963, plain, (![A_186]: (r2_hidden(k1_funct_1(k1_xboole_0, A_186), k1_xboole_0) | ~r2_hidden(A_186, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_958])).
% 6.94/2.59  tff(c_964, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_963])).
% 6.94/2.59  tff(c_1131, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_964])).
% 6.94/2.59  tff(c_1140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_756, c_1131])).
% 6.94/2.59  tff(c_1141, plain, (![A_186]: (~v1_funct_1(k1_xboole_0) | r2_hidden(k1_funct_1(k1_xboole_0, A_186), k1_xboole_0) | ~r2_hidden(A_186, k1_xboole_0))), inference(splitRight, [status(thm)], [c_963])).
% 6.94/2.59  tff(c_1153, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1141])).
% 6.94/2.59  tff(c_1309, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1153])).
% 6.94/2.59  tff(c_1443, plain, (~v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1309])).
% 6.94/2.59  tff(c_1480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1443])).
% 6.94/2.59  tff(c_1483, plain, (![A_250]: (r2_hidden(k1_funct_1(k1_xboole_0, A_250), k1_xboole_0) | ~r2_hidden(A_250, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1141])).
% 6.94/2.59  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.94/2.59  tff(c_1490, plain, (![A_251, B_252]: (r2_hidden(k1_funct_1(k1_xboole_0, A_251), B_252) | ~r1_tarski(k1_xboole_0, B_252) | ~r2_hidden(A_251, k1_xboole_0))), inference(resolution, [status(thm)], [c_1483, c_2])).
% 6.94/2.59  tff(c_1515, plain, (![A_258, B_259, B_260]: (r2_hidden(k1_funct_1(k1_xboole_0, A_258), B_259) | ~r1_tarski(B_260, B_259) | ~r1_tarski(k1_xboole_0, B_260) | ~r2_hidden(A_258, k1_xboole_0))), inference(resolution, [status(thm)], [c_1490, c_2])).
% 6.94/2.59  tff(c_1526, plain, (![A_258]: (r2_hidden(k1_funct_1(k1_xboole_0, A_258), k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, '#skF_4') | ~r2_hidden(A_258, k1_xboole_0))), inference(resolution, [status(thm)], [c_188, c_1515])).
% 6.94/2.59  tff(c_1529, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_1526])).
% 6.94/2.59  tff(c_1594, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1529])).
% 6.94/2.59  tff(c_1837, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1828, c_1594])).
% 6.94/2.59  tff(c_1872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1837])).
% 6.94/2.59  tff(c_1874, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_1526])).
% 6.94/2.59  tff(c_1918, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_1874])).
% 6.94/2.59  tff(c_120, plain, (![D_59, B_60]: (r2_hidden('#skF_5'(D_59), B_60) | ~r1_tarski('#skF_2', B_60) | ~r2_hidden(D_59, '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_106])).
% 6.94/2.59  tff(c_126, plain, (![D_59, B_2, B_60]: (r2_hidden('#skF_5'(D_59), B_2) | ~r1_tarski(B_60, B_2) | ~r1_tarski('#skF_2', B_60) | ~r2_hidden(D_59, '#skF_3'))), inference(resolution, [status(thm)], [c_120, c_2])).
% 6.94/2.59  tff(c_193, plain, (![D_59]: (r2_hidden('#skF_5'(D_59), k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_2', '#skF_4') | ~r2_hidden(D_59, '#skF_3'))), inference(resolution, [status(thm)], [c_188, c_126])).
% 6.94/2.59  tff(c_196, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_193])).
% 6.94/2.59  tff(c_2106, plain, (![C_301, A_302]: (C_301='#skF_3' | ~v1_funct_2(C_301, A_302, '#skF_3') | A_302='#skF_3' | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_302, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_1914, c_1914, c_1914, c_42])).
% 6.94/2.59  tff(c_2113, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_2106])).
% 6.94/2.59  tff(c_2117, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2113])).
% 6.94/2.59  tff(c_2118, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_2117])).
% 6.94/2.59  tff(c_1990, plain, (![C_297, A_298]: (C_297='#skF_3' | ~v1_funct_2(C_297, A_298, '#skF_3') | A_298='#skF_3' | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_298, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_1914, c_1914, c_1914, c_42])).
% 6.94/2.59  tff(c_1997, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_1990])).
% 6.94/2.59  tff(c_2001, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1997])).
% 6.94/2.59  tff(c_2002, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_2001])).
% 6.94/2.59  tff(c_1961, plain, (![D_59]: (r2_hidden('#skF_5'(D_59), '#skF_4') | ~r1_tarski('#skF_2', '#skF_3') | ~r2_hidden(D_59, '#skF_3'))), inference(resolution, [status(thm)], [c_1918, c_126])).
% 6.94/2.59  tff(c_1988, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_1961])).
% 6.94/2.59  tff(c_2003, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2002, c_1988])).
% 6.94/2.59  tff(c_2030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2003])).
% 6.94/2.59  tff(c_2031, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2001])).
% 6.94/2.59  tff(c_1891, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_1874, c_8])).
% 6.94/2.59  tff(c_1892, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1891])).
% 6.94/2.59  tff(c_1916, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_1892])).
% 6.94/2.59  tff(c_2039, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_1916])).
% 6.94/2.59  tff(c_2074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2039])).
% 6.94/2.59  tff(c_2076, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1961])).
% 6.94/2.59  tff(c_2090, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2076, c_8])).
% 6.94/2.59  tff(c_2091, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2090])).
% 6.94/2.59  tff(c_2119, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_2091])).
% 6.94/2.59  tff(c_2147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2119])).
% 6.94/2.59  tff(c_2148, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2117])).
% 6.94/2.59  tff(c_2155, plain, (r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2148, c_2076])).
% 6.94/2.59  tff(c_2193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_2155])).
% 6.94/2.59  tff(c_2194, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_2090])).
% 6.94/2.59  tff(c_2210, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2194, c_196])).
% 6.94/2.59  tff(c_2224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1918, c_2210])).
% 6.94/2.59  tff(c_2225, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1891])).
% 6.94/2.59  tff(c_2241, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2225, c_2225, c_26])).
% 6.94/2.59  tff(c_2240, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2225, c_2225, c_24])).
% 6.94/2.59  tff(c_2259, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2240, c_153])).
% 6.94/2.59  tff(c_50, plain, (![B_33, A_32, C_34]: (k1_xboole_0=B_33 | k1_relset_1(A_32, B_33, C_34)=A_32 | ~v1_funct_2(C_34, A_32, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_2272, plain, (![B_303, A_304, C_305]: (B_303='#skF_4' | k1_relset_1(A_304, B_303, C_305)=A_304 | ~v1_funct_2(C_305, A_304, B_303) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_304, B_303))))), inference(demodulation, [status(thm), theory('equality')], [c_2225, c_50])).
% 6.94/2.59  tff(c_2279, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_2272])).
% 6.94/2.59  tff(c_2283, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_2279])).
% 6.94/2.59  tff(c_2284, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2259, c_2283])).
% 6.94/2.59  tff(c_2316, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_2284])).
% 6.94/2.59  tff(c_2325, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2316, c_196])).
% 6.94/2.59  tff(c_2336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2325])).
% 6.94/2.59  tff(c_2353, plain, (![D_306]: (r2_hidden(D_306, k2_relat_1('#skF_4')) | ~r2_hidden(D_306, '#skF_3'))), inference(splitRight, [status(thm)], [c_939])).
% 6.94/2.59  tff(c_2419, plain, (![A_314]: (r1_tarski(A_314, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_314, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_2353, c_4])).
% 6.94/2.59  tff(c_2435, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_2419])).
% 6.94/2.59  tff(c_2442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_236, c_2435])).
% 6.94/2.59  tff(c_2444, plain, (r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_193])).
% 6.94/2.59  tff(c_4675, plain, (![B_547, A_548, C_549]: (k1_xboole_0=B_547 | k1_relset_1(A_548, B_547, C_549)=A_548 | ~v1_funct_2(C_549, A_548, B_547) | ~m1_subset_1(C_549, k1_zfmisc_1(k2_zfmisc_1(A_548, B_547))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_4682, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_4675])).
% 6.94/2.59  tff(c_4686, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_4682])).
% 6.94/2.59  tff(c_4707, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_4686])).
% 6.94/2.59  tff(c_3482, plain, (![A_455, C_456]: (r2_hidden(k4_tarski(A_455, k1_funct_1(C_456, A_455)), C_456) | ~r2_hidden(A_455, k1_relat_1(C_456)) | ~v1_funct_1(C_456) | ~v1_relat_1(C_456))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.94/2.59  tff(c_3498, plain, (![D_38]: (r2_hidden(k4_tarski('#skF_5'(D_38), D_38), '#skF_4') | ~r2_hidden('#skF_5'(D_38), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_38, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_3482])).
% 6.94/2.59  tff(c_3550, plain, (![D_459]: (r2_hidden(k4_tarski('#skF_5'(D_459), D_459), '#skF_4') | ~r2_hidden('#skF_5'(D_459), k1_relat_1('#skF_4')) | ~r2_hidden(D_459, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58, c_3498])).
% 6.94/2.59  tff(c_3556, plain, (![D_459]: (r2_hidden(D_459, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~r2_hidden('#skF_5'(D_459), k1_relat_1('#skF_4')) | ~r2_hidden(D_459, '#skF_3'))), inference(resolution, [status(thm)], [c_3550, c_20])).
% 6.94/2.59  tff(c_3575, plain, (![D_460]: (r2_hidden(D_460, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_460), k1_relat_1('#skF_4')) | ~r2_hidden(D_460, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_3556])).
% 6.94/2.59  tff(c_3600, plain, (![D_38]: (r2_hidden(D_38, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_38, '#skF_3'))), inference(resolution, [status(thm)], [c_112, c_3575])).
% 6.94/2.59  tff(c_3601, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3600])).
% 6.94/2.59  tff(c_4713, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4707, c_3601])).
% 6.94/2.59  tff(c_4719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4713])).
% 6.94/2.59  tff(c_4720, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4686])).
% 6.94/2.59  tff(c_4824, plain, (![C_554, A_555]: (C_554='#skF_3' | ~v1_funct_2(C_554, A_555, '#skF_3') | A_555='#skF_3' | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_555, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_4720, c_4720, c_4720, c_4720, c_42])).
% 6.94/2.59  tff(c_4831, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_4824])).
% 6.94/2.59  tff(c_4835, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4831])).
% 6.94/2.59  tff(c_4836, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_4835])).
% 6.94/2.59  tff(c_4148, plain, (![B_521, A_522, C_523]: (k1_xboole_0=B_521 | k1_relset_1(A_522, B_521, C_523)=A_522 | ~v1_funct_2(C_523, A_522, B_521) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_522, B_521))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_4155, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_4148])).
% 6.94/2.59  tff(c_4159, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_4155])).
% 6.94/2.59  tff(c_4160, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_4159])).
% 6.94/2.59  tff(c_4166, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4160, c_3601])).
% 6.94/2.59  tff(c_4172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4166])).
% 6.94/2.59  tff(c_4173, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4159])).
% 6.94/2.59  tff(c_4447, plain, (![C_543, A_544]: (C_543='#skF_3' | ~v1_funct_2(C_543, A_544, '#skF_3') | A_544='#skF_3' | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_544, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4173, c_4173, c_4173, c_42])).
% 6.94/2.59  tff(c_4454, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_4447])).
% 6.94/2.59  tff(c_4458, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4454])).
% 6.94/2.59  tff(c_4459, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_4458])).
% 6.94/2.59  tff(c_3837, plain, (![B_500, A_501, C_502]: (k1_xboole_0=B_500 | k1_relset_1(A_501, B_500, C_502)=A_501 | ~v1_funct_2(C_502, A_501, B_500) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_501, B_500))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_3844, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_3837])).
% 6.94/2.59  tff(c_3848, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_3844])).
% 6.94/2.59  tff(c_3849, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_3848])).
% 6.94/2.59  tff(c_3855, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3849, c_3601])).
% 6.94/2.59  tff(c_3861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3855])).
% 6.94/2.59  tff(c_3862, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3848])).
% 6.94/2.59  tff(c_3894, plain, (![C_504, A_505]: (C_504='#skF_3' | ~v1_funct_2(C_504, A_505, '#skF_3') | A_505='#skF_3' | ~m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(A_505, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3862, c_3862, c_3862, c_42])).
% 6.94/2.59  tff(c_3901, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_3894])).
% 6.94/2.59  tff(c_3905, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3901])).
% 6.94/2.59  tff(c_3906, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_3905])).
% 6.94/2.59  tff(c_3863, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_3848])).
% 6.94/2.59  tff(c_3907, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_3863])).
% 6.94/2.59  tff(c_3941, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_56])).
% 6.94/2.59  tff(c_3935, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_162])).
% 6.94/2.59  tff(c_3940, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_54])).
% 6.94/2.59  tff(c_4039, plain, (![B_508, C_509]: (k1_relset_1('#skF_3', B_508, C_509)='#skF_3' | ~v1_funct_2(C_509, '#skF_3', B_508) | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_508))))), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3862, c_3862, c_3862, c_48])).
% 6.94/2.59  tff(c_4042, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3940, c_4039])).
% 6.94/2.59  tff(c_4049, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3941, c_3935, c_4042])).
% 6.94/2.59  tff(c_4051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3907, c_4049])).
% 6.94/2.59  tff(c_4052, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_3905])).
% 6.94/2.59  tff(c_2906, plain, (![B_388, A_389, C_390]: (k1_xboole_0=B_388 | k1_relset_1(A_389, B_388, C_390)=A_389 | ~v1_funct_2(C_390, A_389, B_388) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_389, B_388))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_2913, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_2906])).
% 6.94/2.59  tff(c_2917, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_2913])).
% 6.94/2.59  tff(c_2918, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_2917])).
% 6.94/2.59  tff(c_2643, plain, (![A_358, C_359]: (r2_hidden(k4_tarski(A_358, k1_funct_1(C_359, A_358)), C_359) | ~r2_hidden(A_358, k1_relat_1(C_359)) | ~v1_funct_1(C_359) | ~v1_relat_1(C_359))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.94/2.59  tff(c_2659, plain, (![D_38]: (r2_hidden(k4_tarski('#skF_5'(D_38), D_38), '#skF_4') | ~r2_hidden('#skF_5'(D_38), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_38, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2643])).
% 6.94/2.59  tff(c_2699, plain, (![D_365]: (r2_hidden(k4_tarski('#skF_5'(D_365), D_365), '#skF_4') | ~r2_hidden('#skF_5'(D_365), k1_relat_1('#skF_4')) | ~r2_hidden(D_365, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58, c_2659])).
% 6.94/2.59  tff(c_2705, plain, (![D_365]: (r2_hidden(D_365, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~r2_hidden('#skF_5'(D_365), k1_relat_1('#skF_4')) | ~r2_hidden(D_365, '#skF_3'))), inference(resolution, [status(thm)], [c_2699, c_20])).
% 6.94/2.59  tff(c_2740, plain, (![D_367]: (r2_hidden(D_367, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_367), k1_relat_1('#skF_4')) | ~r2_hidden(D_367, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2705])).
% 6.94/2.59  tff(c_2765, plain, (![D_38]: (r2_hidden(D_38, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_38, '#skF_3'))), inference(resolution, [status(thm)], [c_112, c_2740])).
% 6.94/2.59  tff(c_2766, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2765])).
% 6.94/2.59  tff(c_2924, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2918, c_2766])).
% 6.94/2.59  tff(c_2930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2924])).
% 6.94/2.59  tff(c_2931, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2917])).
% 6.94/2.59  tff(c_2976, plain, (![C_393, A_394]: (C_393='#skF_3' | ~v1_funct_2(C_393, A_394, '#skF_3') | A_394='#skF_3' | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_394, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2931, c_2931, c_2931, c_2931, c_42])).
% 6.94/2.59  tff(c_2983, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_2976])).
% 6.94/2.59  tff(c_2987, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2983])).
% 6.94/2.59  tff(c_3000, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_2987])).
% 6.94/2.59  tff(c_2932, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_2917])).
% 6.94/2.59  tff(c_3002, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3000, c_2932])).
% 6.94/2.59  tff(c_3035, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3000, c_56])).
% 6.94/2.59  tff(c_3034, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3000, c_54])).
% 6.94/2.59  tff(c_2936, plain, (![B_33, C_34]: (k1_relset_1('#skF_3', B_33, C_34)='#skF_3' | ~v1_funct_2(C_34, '#skF_3', B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_33))))), inference(demodulation, [status(thm), theory('equality')], [c_2931, c_2931, c_2931, c_2931, c_48])).
% 6.94/2.59  tff(c_3068, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3034, c_2936])).
% 6.94/2.59  tff(c_3094, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3035, c_3068])).
% 6.94/2.59  tff(c_3029, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3000, c_162])).
% 6.94/2.59  tff(c_3124, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_3029])).
% 6.94/2.59  tff(c_3125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3002, c_3124])).
% 6.94/2.59  tff(c_3126, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2987])).
% 6.94/2.59  tff(c_2492, plain, (v1_relat_1(k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2484, c_16])).
% 6.94/2.59  tff(c_2513, plain, (~v1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2492])).
% 6.94/2.59  tff(c_3155, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3126, c_2513])).
% 6.94/2.59  tff(c_3175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_3155])).
% 6.94/2.59  tff(c_3201, plain, (![D_402]: (r2_hidden(D_402, k2_relat_1('#skF_4')) | ~r2_hidden(D_402, '#skF_3'))), inference(splitRight, [status(thm)], [c_2765])).
% 6.94/2.59  tff(c_3236, plain, (![A_404]: (r1_tarski(A_404, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_404, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_3201, c_4])).
% 6.94/2.59  tff(c_3252, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_3236])).
% 6.94/2.59  tff(c_3259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2500, c_2500, c_3252])).
% 6.94/2.59  tff(c_3261, plain, (v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2492])).
% 6.94/2.59  tff(c_3745, plain, (![B_489, A_490, C_491]: (k1_xboole_0=B_489 | k1_relset_1(A_490, B_489, C_491)=A_490 | ~v1_funct_2(C_491, A_490, B_489) | ~m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(A_490, B_489))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.94/2.59  tff(c_3752, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_3745])).
% 6.94/2.59  tff(c_3756, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_162, c_3752])).
% 6.94/2.59  tff(c_3757, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_3756])).
% 6.94/2.59  tff(c_3763, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3757, c_3601])).
% 6.94/2.59  tff(c_3769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3763])).
% 6.94/2.59  tff(c_3770, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3756])).
% 6.94/2.59  tff(c_3637, plain, (![C_468, A_469]: (r2_hidden(k1_funct_1(C_468, A_469), k2_relat_1(C_468)) | ~r2_hidden(A_469, k1_relat_1(C_468)) | ~v1_funct_1(C_468) | ~v1_relat_1(C_468))), inference(resolution, [status(thm)], [c_3482, c_20])).
% 6.94/2.59  tff(c_3647, plain, (![A_469]: (r2_hidden(k1_funct_1(k1_xboole_0, A_469), k1_xboole_0) | ~r2_hidden(A_469, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3637])).
% 6.94/2.59  tff(c_3652, plain, (![A_469]: (r2_hidden(k1_funct_1(k1_xboole_0, A_469), k1_xboole_0) | ~r2_hidden(A_469, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3647])).
% 6.94/2.59  tff(c_3664, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3652])).
% 6.94/2.59  tff(c_3773, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3770, c_3664])).
% 6.94/2.59  tff(c_3783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3261, c_3773])).
% 6.94/2.59  tff(c_3784, plain, (![A_469]: (~v1_funct_1(k1_xboole_0) | r2_hidden(k1_funct_1(k1_xboole_0, A_469), k1_xboole_0) | ~r2_hidden(A_469, k1_xboole_0))), inference(splitRight, [status(thm)], [c_3652])).
% 6.94/2.59  tff(c_3805, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3784])).
% 6.94/2.59  tff(c_3865, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3805])).
% 6.94/2.59  tff(c_4058, plain, (~v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4052, c_3865])).
% 6.94/2.59  tff(c_4103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_4058])).
% 6.94/2.59  tff(c_4106, plain, (![A_510]: (r2_hidden(k1_funct_1(k1_xboole_0, A_510), k1_xboole_0) | ~r2_hidden(A_510, k1_xboole_0))), inference(splitRight, [status(thm)], [c_3784])).
% 6.94/2.59  tff(c_4114, plain, (![A_514, B_515]: (r2_hidden(k1_funct_1(k1_xboole_0, A_514), B_515) | ~r1_tarski(k1_xboole_0, B_515) | ~r2_hidden(A_514, k1_xboole_0))), inference(resolution, [status(thm)], [c_4106, c_2])).
% 6.94/2.59  tff(c_4128, plain, (![A_518, B_519, B_520]: (r2_hidden(k1_funct_1(k1_xboole_0, A_518), B_519) | ~r1_tarski(B_520, B_519) | ~r1_tarski(k1_xboole_0, B_520) | ~r2_hidden(A_518, k1_xboole_0))), inference(resolution, [status(thm)], [c_4114, c_2])).
% 6.94/2.59  tff(c_4144, plain, (![A_518]: (r2_hidden(k1_funct_1(k1_xboole_0, A_518), '#skF_4') | ~r1_tarski(k1_xboole_0, '#skF_2') | ~r2_hidden(A_518, k1_xboole_0))), inference(resolution, [status(thm)], [c_2444, c_4128])).
% 6.94/2.59  tff(c_4147, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_4144])).
% 6.94/2.59  tff(c_4176, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4147])).
% 6.94/2.59  tff(c_4461, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_4176])).
% 6.94/2.59  tff(c_4500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4461])).
% 6.94/2.59  tff(c_4501, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4458])).
% 6.94/2.59  tff(c_4252, plain, (![C_532, A_533]: (C_532='#skF_3' | ~v1_funct_2(C_532, A_533, '#skF_3') | A_533='#skF_3' | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_533, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4173, c_4173, c_4173, c_42])).
% 6.94/2.59  tff(c_4259, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_4252])).
% 6.94/2.59  tff(c_4263, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4259])).
% 6.94/2.59  tff(c_4264, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_4263])).
% 6.94/2.59  tff(c_4265, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4264, c_4176])).
% 6.94/2.59  tff(c_4304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4265])).
% 6.94/2.59  tff(c_4305, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4263])).
% 6.94/2.59  tff(c_4145, plain, (![A_518]: (r2_hidden(k1_funct_1(k1_xboole_0, A_518), k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, '#skF_4') | ~r2_hidden(A_518, k1_xboole_0))), inference(resolution, [status(thm)], [c_188, c_4128])).
% 6.94/2.59  tff(c_4195, plain, (![A_518]: (r2_hidden(k1_funct_1('#skF_3', A_518), k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_4') | ~r2_hidden(A_518, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4173, c_4173, c_4145])).
% 6.94/2.59  tff(c_4196, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_4195])).
% 6.94/2.59  tff(c_4314, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4305, c_4196])).
% 6.94/2.59  tff(c_4361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4314])).
% 6.94/2.59  tff(c_4363, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_4195])).
% 6.94/2.59  tff(c_4391, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4363, c_8])).
% 6.94/2.59  tff(c_4393, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_4391])).
% 6.94/2.59  tff(c_4509, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4501, c_4393])).
% 6.94/2.59  tff(c_4559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4509])).
% 6.94/2.59  tff(c_4560, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4391])).
% 6.94/2.59  tff(c_4189, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4173, c_4173, c_26])).
% 6.94/2.59  tff(c_4585, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4560, c_4560, c_4189])).
% 6.94/2.59  tff(c_2446, plain, (![D_59]: (r2_hidden('#skF_5'(D_59), '#skF_4') | ~r1_tarski('#skF_2', '#skF_2') | ~r2_hidden(D_59, '#skF_3'))), inference(resolution, [status(thm)], [c_2444, c_126])).
% 6.94/2.59  tff(c_2454, plain, (![D_315]: (r2_hidden('#skF_5'(D_315), '#skF_4') | ~r2_hidden(D_315, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2446])).
% 6.94/2.59  tff(c_2460, plain, (![D_315, B_2]: (r2_hidden('#skF_5'(D_315), B_2) | ~r1_tarski('#skF_4', B_2) | ~r2_hidden(D_315, '#skF_3'))), inference(resolution, [status(thm)], [c_2454, c_2])).
% 6.94/2.59  tff(c_3598, plain, (![D_315]: (r2_hidden(D_315, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_4')) | ~r2_hidden(D_315, '#skF_3'))), inference(resolution, [status(thm)], [c_2460, c_3575])).
% 6.94/2.59  tff(c_3602, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3598])).
% 6.94/2.59  tff(c_4644, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4585, c_3602])).
% 6.94/2.59  tff(c_4648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4644])).
% 6.94/2.59  tff(c_4650, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_4144])).
% 6.94/2.59  tff(c_4674, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_4650, c_8])).
% 6.94/2.59  tff(c_4821, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4720, c_4720, c_4674])).
% 6.94/2.59  tff(c_4822, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_4821])).
% 6.94/2.59  tff(c_4837, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4836, c_4822])).
% 6.94/2.59  tff(c_4877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4837])).
% 6.94/2.59  tff(c_4878, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4835])).
% 6.94/2.59  tff(c_136, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_1'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_106])).
% 6.94/2.59  tff(c_3360, plain, (![A_434, B_435, B_436, B_437]: (r2_hidden('#skF_1'(A_434, B_435), B_436) | ~r1_tarski(B_437, B_436) | ~r1_tarski(A_434, B_437) | r1_tarski(A_434, B_435))), inference(resolution, [status(thm)], [c_136, c_2])).
% 6.94/2.59  tff(c_3379, plain, (![A_440, B_441]: (r2_hidden('#skF_1'(A_440, B_441), '#skF_4') | ~r1_tarski(A_440, '#skF_2') | r1_tarski(A_440, B_441))), inference(resolution, [status(thm)], [c_2444, c_3360])).
% 6.94/2.59  tff(c_3390, plain, (![A_440]: (~r1_tarski(A_440, '#skF_2') | r1_tarski(A_440, '#skF_4'))), inference(resolution, [status(thm)], [c_3379, c_4])).
% 6.94/2.59  tff(c_4669, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_4650, c_3390])).
% 6.94/2.59  tff(c_4732, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4720, c_4669])).
% 6.94/2.59  tff(c_4800, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4732, c_8])).
% 6.94/2.59  tff(c_4823, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_4800])).
% 6.94/2.59  tff(c_4882, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4878, c_4823])).
% 6.94/2.59  tff(c_4934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4882])).
% 6.94/2.59  tff(c_4935, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4800])).
% 6.94/2.59  tff(c_4937, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4935, c_4822])).
% 6.94/2.59  tff(c_4988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2444, c_4937])).
% 6.94/2.59  tff(c_4989, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4821])).
% 6.94/2.59  tff(c_4721, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_4686])).
% 6.94/2.59  tff(c_4992, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4989, c_4721])).
% 6.94/2.59  tff(c_5027, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4989, c_56])).
% 6.94/2.59  tff(c_5021, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4989, c_162])).
% 6.94/2.59  tff(c_5026, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4989, c_54])).
% 6.94/2.59  tff(c_5144, plain, (![B_562, C_563]: (k1_relset_1('#skF_3', B_562, C_563)='#skF_3' | ~v1_funct_2(C_563, '#skF_3', B_562) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_562))))), inference(demodulation, [status(thm), theory('equality')], [c_4720, c_4720, c_4720, c_4720, c_48])).
% 6.94/2.59  tff(c_5147, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_5026, c_5144])).
% 6.94/2.59  tff(c_5154, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5027, c_5021, c_5147])).
% 6.94/2.59  tff(c_5156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4992, c_5154])).
% 6.94/2.59  tff(c_5158, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3598])).
% 6.94/2.59  tff(c_3456, plain, (![A_450, B_451, B_452]: (r2_hidden('#skF_1'(A_450, B_451), B_452) | ~r1_tarski('#skF_4', B_452) | ~r1_tarski(A_450, '#skF_2') | r1_tarski(A_450, B_451))), inference(resolution, [status(thm)], [c_3379, c_2])).
% 6.94/2.59  tff(c_3467, plain, (![B_452, A_450]: (~r1_tarski('#skF_4', B_452) | ~r1_tarski(A_450, '#skF_2') | r1_tarski(A_450, B_452))), inference(resolution, [status(thm)], [c_3456, c_4])).
% 6.94/2.59  tff(c_5214, plain, (![A_565]: (~r1_tarski(A_565, '#skF_2') | r1_tarski(A_565, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_5158, c_3467])).
% 6.94/2.59  tff(c_5217, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_5214, c_3601])).
% 6.94/2.59  tff(c_5242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_5217])).
% 6.94/2.59  tff(c_5263, plain, (![D_566]: (r2_hidden(D_566, k2_relat_1('#skF_4')) | ~r2_hidden(D_566, '#skF_3'))), inference(splitRight, [status(thm)], [c_3600])).
% 6.94/2.59  tff(c_5333, plain, (![A_574]: (r1_tarski(A_574, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_574, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_5263, c_4])).
% 6.94/2.59  tff(c_5353, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_5333])).
% 6.94/2.59  tff(c_5361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2500, c_2500, c_5353])).
% 6.94/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.59  
% 6.94/2.59  Inference rules
% 6.94/2.59  ----------------------
% 6.94/2.59  #Ref     : 0
% 6.94/2.59  #Sup     : 959
% 6.94/2.59  #Fact    : 0
% 6.94/2.59  #Define  : 0
% 6.94/2.59  #Split   : 78
% 6.94/2.59  #Chain   : 0
% 6.94/2.59  #Close   : 0
% 6.94/2.59  
% 6.94/2.59  Ordering : KBO
% 6.94/2.59  
% 6.94/2.59  Simplification rules
% 6.94/2.59  ----------------------
% 6.94/2.59  #Subsume      : 215
% 6.94/2.59  #Demod        : 1869
% 6.94/2.59  #Tautology    : 221
% 6.94/2.59  #SimpNegUnit  : 15
% 6.94/2.59  #BackRed      : 1149
% 6.94/2.59  
% 6.94/2.59  #Partial instantiations: 0
% 6.94/2.59  #Strategies tried      : 1
% 6.94/2.59  
% 6.94/2.59  Timing (in seconds)
% 6.94/2.59  ----------------------
% 7.31/2.59  Preprocessing        : 0.47
% 7.31/2.59  Parsing              : 0.27
% 7.31/2.59  CNF conversion       : 0.03
% 7.31/2.59  Main loop            : 1.23
% 7.31/2.59  Inferencing          : 0.36
% 7.31/2.59  Reduction            : 0.41
% 7.31/2.59  Demodulation         : 0.27
% 7.31/2.59  BG Simplification    : 0.06
% 7.31/2.59  Subsumption          : 0.29
% 7.31/2.59  Abstraction          : 0.06
% 7.31/2.59  MUC search           : 0.00
% 7.31/2.59  Cooper               : 0.00
% 7.31/2.59  Total                : 1.83
% 7.31/2.59  Index Insertion      : 0.00
% 7.31/2.59  Index Deletion       : 0.00
% 7.31/2.59  Index Matching       : 0.00
% 7.31/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
