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
% DateTime   : Thu Dec  3 10:16:26 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 334 expanded)
%              Number of leaves         :   39 ( 130 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 847 expanded)
%              Number of equality atoms :   21 (  89 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_22,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_89,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_89])).

tff(c_99,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_95])).

tff(c_139,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_148,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_139])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_653,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( k7_relset_1(A_174,B_175,C_176,D_177) = k9_relat_1(C_176,D_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_664,plain,(
    ! [D_177] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_177) = k9_relat_1('#skF_6',D_177) ),
    inference(resolution,[status(thm)],[c_48,c_653])).

tff(c_46,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_667,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_46])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden('#skF_2'(A_22,B_23,C_24),k1_relat_1(C_24))
      | ~ r2_hidden(A_22,k9_relat_1(C_24,B_23))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_933,plain,(
    ! [A_220,B_221,C_222] :
      ( r2_hidden(k4_tarski('#skF_2'(A_220,B_221,C_222),A_220),C_222)
      | ~ r2_hidden(A_220,k9_relat_1(C_222,B_221))
      | ~ v1_relat_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [C_30,A_28,B_29] :
      ( k1_funct_1(C_30,A_28) = B_29
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1408,plain,(
    ! [C_284,A_285,B_286] :
      ( k1_funct_1(C_284,'#skF_2'(A_285,B_286,C_284)) = A_285
      | ~ v1_funct_1(C_284)
      | ~ r2_hidden(A_285,k9_relat_1(C_284,B_286))
      | ~ v1_relat_1(C_284) ) ),
    inference(resolution,[status(thm)],[c_933,c_34])).

tff(c_1418,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_667,c_1408])).

tff(c_1433,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_52,c_1418])).

tff(c_32,plain,(
    ! [A_28,C_30] :
      ( r2_hidden(k4_tarski(A_28,k1_funct_1(C_30,A_28)),C_30)
      | ~ r2_hidden(A_28,k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1440,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_32])).

tff(c_1444,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_52,c_1440])).

tff(c_1446,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1444])).

tff(c_1449,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_1446])).

tff(c_1456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_667,c_1449])).

tff(c_1458,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1444])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_179,plain,(
    ! [A_79,C_80,B_81] :
      ( m1_subset_1(A_79,C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_184,plain,(
    ! [A_79,B_11,A_10] :
      ( m1_subset_1(A_79,B_11)
      | ~ r2_hidden(A_79,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_1497,plain,(
    ! [B_287] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),B_287)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_287) ) ),
    inference(resolution,[status(thm)],[c_1458,c_184])).

tff(c_1501,plain,(
    ! [A_18] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_18)
      | ~ v4_relat_1('#skF_6',A_18)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1497])).

tff(c_1521,plain,(
    ! [A_291] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_291)
      | ~ v4_relat_1('#skF_6',A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_1501])).

tff(c_156,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_79,plain,(
    ! [B_54,A_55] :
      ( v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [A_10,B_11] :
      ( v1_xboole_0(A_10)
      | ~ v1_xboole_0(B_11)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_227,plain,(
    ! [B_88,A_89] :
      ( v1_xboole_0(k1_relat_1(B_88))
      | ~ v1_xboole_0(A_89)
      | ~ v4_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_156,c_86])).

tff(c_229,plain,
    ( v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_148,c_227])).

tff(c_232,plain,
    ( v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_229])).

tff(c_233,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_325,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_2'(A_109,B_110,C_111),B_110)
      | ~ r2_hidden(A_109,k9_relat_1(C_111,B_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [F_42] :
      ( k1_funct_1('#skF_6',F_42) != '#skF_7'
      | ~ r2_hidden(F_42,'#skF_5')
      | ~ r2_hidden(F_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_622,plain,(
    ! [A_164,C_165] :
      ( k1_funct_1('#skF_6','#skF_2'(A_164,'#skF_5',C_165)) != '#skF_7'
      | ~ r2_hidden('#skF_2'(A_164,'#skF_5',C_165),'#skF_3')
      | ~ r2_hidden(A_164,k9_relat_1(C_165,'#skF_5'))
      | ~ v1_relat_1(C_165) ) ),
    inference(resolution,[status(thm)],[c_325,c_44])).

tff(c_625,plain,(
    ! [A_164,C_165] :
      ( k1_funct_1('#skF_6','#skF_2'(A_164,'#skF_5',C_165)) != '#skF_7'
      | ~ r2_hidden(A_164,k9_relat_1(C_165,'#skF_5'))
      | ~ v1_relat_1(C_165)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1('#skF_2'(A_164,'#skF_5',C_165),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_622])).

tff(c_1058,plain,(
    ! [A_232,C_233] :
      ( k1_funct_1('#skF_6','#skF_2'(A_232,'#skF_5',C_233)) != '#skF_7'
      | ~ r2_hidden(A_232,k9_relat_1(C_233,'#skF_5'))
      | ~ v1_relat_1(C_233)
      | ~ m1_subset_1('#skF_2'(A_232,'#skF_5',C_233),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_625])).

tff(c_1069,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_667,c_1058])).

tff(c_1086,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_1069])).

tff(c_1091,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_1524,plain,(
    ~ v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1521,c_1091])).

tff(c_1558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1524])).

tff(c_1559,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_1851,plain,(
    ! [C_333,A_334,B_335] :
      ( k1_funct_1(C_333,'#skF_2'(A_334,B_335,C_333)) = A_334
      | ~ v1_funct_1(C_333)
      | ~ r2_hidden(A_334,k9_relat_1(C_333,B_335))
      | ~ v1_relat_1(C_333) ) ),
    inference(resolution,[status(thm)],[c_933,c_34])).

tff(c_1861,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_667,c_1851])).

tff(c_1876,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_52,c_1861])).

tff(c_1878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1559,c_1876])).

tff(c_1879,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2032,plain,(
    ! [A_375,B_376,C_377] :
      ( r2_hidden('#skF_2'(A_375,B_376,C_377),k1_relat_1(C_377))
      | ~ r2_hidden(A_375,k9_relat_1(C_377,B_376))
      | ~ v1_relat_1(C_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2040,plain,(
    ! [C_378,A_379,B_380] :
      ( ~ v1_xboole_0(k1_relat_1(C_378))
      | ~ r2_hidden(A_379,k9_relat_1(C_378,B_380))
      | ~ v1_relat_1(C_378) ) ),
    inference(resolution,[status(thm)],[c_2032,c_2])).

tff(c_2055,plain,(
    ! [C_378,B_380] :
      ( ~ v1_xboole_0(k1_relat_1(C_378))
      | ~ v1_relat_1(C_378)
      | v1_xboole_0(k9_relat_1(C_378,B_380)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2040])).

tff(c_2093,plain,(
    ! [A_395,B_396,C_397,D_398] :
      ( k7_relset_1(A_395,B_396,C_397,D_398) = k9_relat_1(C_397,D_398)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2104,plain,(
    ! [D_398] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_398) = k9_relat_1('#skF_6',D_398) ),
    inference(resolution,[status(thm)],[c_48,c_2093])).

tff(c_73,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_2106,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_73])).

tff(c_2165,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2055,c_2106])).

tff(c_2172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_1879,c_2165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.72  
% 4.28/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.28/1.72  
% 4.28/1.72  %Foreground sorts:
% 4.28/1.72  
% 4.28/1.72  
% 4.28/1.72  %Background operators:
% 4.28/1.72  
% 4.28/1.72  
% 4.28/1.72  %Foreground operators:
% 4.28/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.28/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.28/1.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.28/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.28/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.28/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.72  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.28/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.28/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.28/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.28/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.28/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.28/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.28/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.28/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.28/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.28/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.28/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.28/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.28/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/1.72  
% 4.28/1.74  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.28/1.74  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 4.28/1.74  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.28/1.74  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.28/1.74  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.28/1.74  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.28/1.74  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.28/1.74  tff(f_90, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.28/1.74  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.28/1.74  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.28/1.74  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.28/1.74  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.28/1.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.28/1.74  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.28/1.74  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.28/1.74  tff(c_89, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.28/1.74  tff(c_95, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_89])).
% 4.28/1.74  tff(c_99, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_95])).
% 4.28/1.74  tff(c_139, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.28/1.74  tff(c_148, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_139])).
% 4.28/1.74  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.28/1.74  tff(c_653, plain, (![A_174, B_175, C_176, D_177]: (k7_relset_1(A_174, B_175, C_176, D_177)=k9_relat_1(C_176, D_177) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.28/1.74  tff(c_664, plain, (![D_177]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_177)=k9_relat_1('#skF_6', D_177))), inference(resolution, [status(thm)], [c_48, c_653])).
% 4.28/1.74  tff(c_46, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.28/1.74  tff(c_667, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_664, c_46])).
% 4.28/1.74  tff(c_30, plain, (![A_22, B_23, C_24]: (r2_hidden('#skF_2'(A_22, B_23, C_24), k1_relat_1(C_24)) | ~r2_hidden(A_22, k9_relat_1(C_24, B_23)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.28/1.74  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.28/1.74  tff(c_933, plain, (![A_220, B_221, C_222]: (r2_hidden(k4_tarski('#skF_2'(A_220, B_221, C_222), A_220), C_222) | ~r2_hidden(A_220, k9_relat_1(C_222, B_221)) | ~v1_relat_1(C_222))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.28/1.74  tff(c_34, plain, (![C_30, A_28, B_29]: (k1_funct_1(C_30, A_28)=B_29 | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.28/1.74  tff(c_1408, plain, (![C_284, A_285, B_286]: (k1_funct_1(C_284, '#skF_2'(A_285, B_286, C_284))=A_285 | ~v1_funct_1(C_284) | ~r2_hidden(A_285, k9_relat_1(C_284, B_286)) | ~v1_relat_1(C_284))), inference(resolution, [status(thm)], [c_933, c_34])).
% 4.28/1.74  tff(c_1418, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_667, c_1408])).
% 4.28/1.74  tff(c_1433, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_52, c_1418])).
% 4.28/1.74  tff(c_32, plain, (![A_28, C_30]: (r2_hidden(k4_tarski(A_28, k1_funct_1(C_30, A_28)), C_30) | ~r2_hidden(A_28, k1_relat_1(C_30)) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.28/1.74  tff(c_1440, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1433, c_32])).
% 4.28/1.74  tff(c_1444, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_52, c_1440])).
% 4.28/1.74  tff(c_1446, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1444])).
% 4.28/1.74  tff(c_1449, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_1446])).
% 4.28/1.74  tff(c_1456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_667, c_1449])).
% 4.28/1.74  tff(c_1458, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1444])).
% 4.28/1.74  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.28/1.74  tff(c_179, plain, (![A_79, C_80, B_81]: (m1_subset_1(A_79, C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.28/1.74  tff(c_184, plain, (![A_79, B_11, A_10]: (m1_subset_1(A_79, B_11) | ~r2_hidden(A_79, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_179])).
% 4.28/1.74  tff(c_1497, plain, (![B_287]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_287) | ~r1_tarski(k1_relat_1('#skF_6'), B_287))), inference(resolution, [status(thm)], [c_1458, c_184])).
% 4.28/1.74  tff(c_1501, plain, (![A_18]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_18) | ~v4_relat_1('#skF_6', A_18) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1497])).
% 4.28/1.74  tff(c_1521, plain, (![A_291]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_291) | ~v4_relat_1('#skF_6', A_291))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_1501])).
% 4.28/1.74  tff(c_156, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.28/1.74  tff(c_79, plain, (![B_54, A_55]: (v1_xboole_0(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.28/1.74  tff(c_86, plain, (![A_10, B_11]: (v1_xboole_0(A_10) | ~v1_xboole_0(B_11) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_79])).
% 4.28/1.74  tff(c_227, plain, (![B_88, A_89]: (v1_xboole_0(k1_relat_1(B_88)) | ~v1_xboole_0(A_89) | ~v4_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_156, c_86])).
% 4.28/1.74  tff(c_229, plain, (v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_xboole_0('#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_148, c_227])).
% 4.28/1.74  tff(c_232, plain, (v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_229])).
% 4.28/1.74  tff(c_233, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_232])).
% 4.28/1.74  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.74  tff(c_325, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_2'(A_109, B_110, C_111), B_110) | ~r2_hidden(A_109, k9_relat_1(C_111, B_110)) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.28/1.74  tff(c_44, plain, (![F_42]: (k1_funct_1('#skF_6', F_42)!='#skF_7' | ~r2_hidden(F_42, '#skF_5') | ~r2_hidden(F_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.28/1.74  tff(c_622, plain, (![A_164, C_165]: (k1_funct_1('#skF_6', '#skF_2'(A_164, '#skF_5', C_165))!='#skF_7' | ~r2_hidden('#skF_2'(A_164, '#skF_5', C_165), '#skF_3') | ~r2_hidden(A_164, k9_relat_1(C_165, '#skF_5')) | ~v1_relat_1(C_165))), inference(resolution, [status(thm)], [c_325, c_44])).
% 4.28/1.74  tff(c_625, plain, (![A_164, C_165]: (k1_funct_1('#skF_6', '#skF_2'(A_164, '#skF_5', C_165))!='#skF_7' | ~r2_hidden(A_164, k9_relat_1(C_165, '#skF_5')) | ~v1_relat_1(C_165) | v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_2'(A_164, '#skF_5', C_165), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_622])).
% 4.28/1.74  tff(c_1058, plain, (![A_232, C_233]: (k1_funct_1('#skF_6', '#skF_2'(A_232, '#skF_5', C_233))!='#skF_7' | ~r2_hidden(A_232, k9_relat_1(C_233, '#skF_5')) | ~v1_relat_1(C_233) | ~m1_subset_1('#skF_2'(A_232, '#skF_5', C_233), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_233, c_625])).
% 4.28/1.74  tff(c_1069, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_667, c_1058])).
% 4.28/1.74  tff(c_1086, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_1069])).
% 4.28/1.74  tff(c_1091, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1086])).
% 4.28/1.74  tff(c_1524, plain, (~v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1521, c_1091])).
% 4.28/1.74  tff(c_1558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_1524])).
% 4.28/1.74  tff(c_1559, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_1086])).
% 4.28/1.74  tff(c_1851, plain, (![C_333, A_334, B_335]: (k1_funct_1(C_333, '#skF_2'(A_334, B_335, C_333))=A_334 | ~v1_funct_1(C_333) | ~r2_hidden(A_334, k9_relat_1(C_333, B_335)) | ~v1_relat_1(C_333))), inference(resolution, [status(thm)], [c_933, c_34])).
% 4.28/1.74  tff(c_1861, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_667, c_1851])).
% 4.28/1.74  tff(c_1876, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_52, c_1861])).
% 4.28/1.74  tff(c_1878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1559, c_1876])).
% 4.28/1.74  tff(c_1879, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_232])).
% 4.28/1.74  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.74  tff(c_2032, plain, (![A_375, B_376, C_377]: (r2_hidden('#skF_2'(A_375, B_376, C_377), k1_relat_1(C_377)) | ~r2_hidden(A_375, k9_relat_1(C_377, B_376)) | ~v1_relat_1(C_377))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.28/1.74  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.74  tff(c_2040, plain, (![C_378, A_379, B_380]: (~v1_xboole_0(k1_relat_1(C_378)) | ~r2_hidden(A_379, k9_relat_1(C_378, B_380)) | ~v1_relat_1(C_378))), inference(resolution, [status(thm)], [c_2032, c_2])).
% 4.28/1.74  tff(c_2055, plain, (![C_378, B_380]: (~v1_xboole_0(k1_relat_1(C_378)) | ~v1_relat_1(C_378) | v1_xboole_0(k9_relat_1(C_378, B_380)))), inference(resolution, [status(thm)], [c_4, c_2040])).
% 4.28/1.74  tff(c_2093, plain, (![A_395, B_396, C_397, D_398]: (k7_relset_1(A_395, B_396, C_397, D_398)=k9_relat_1(C_397, D_398) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.28/1.74  tff(c_2104, plain, (![D_398]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_398)=k9_relat_1('#skF_6', D_398))), inference(resolution, [status(thm)], [c_48, c_2093])).
% 4.28/1.74  tff(c_73, plain, (~v1_xboole_0(k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_2])).
% 4.28/1.74  tff(c_2106, plain, (~v1_xboole_0(k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2104, c_73])).
% 4.28/1.74  tff(c_2165, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2055, c_2106])).
% 4.28/1.74  tff(c_2172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_1879, c_2165])).
% 4.28/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.74  
% 4.28/1.74  Inference rules
% 4.28/1.74  ----------------------
% 4.28/1.74  #Ref     : 0
% 4.28/1.74  #Sup     : 417
% 4.28/1.74  #Fact    : 0
% 4.28/1.74  #Define  : 0
% 4.28/1.74  #Split   : 16
% 4.28/1.74  #Chain   : 0
% 4.28/1.74  #Close   : 0
% 4.28/1.74  
% 4.28/1.74  Ordering : KBO
% 4.28/1.74  
% 4.28/1.74  Simplification rules
% 4.28/1.74  ----------------------
% 4.28/1.74  #Subsume      : 65
% 4.28/1.74  #Demod        : 78
% 4.28/1.74  #Tautology    : 29
% 4.28/1.74  #SimpNegUnit  : 16
% 4.28/1.74  #BackRed      : 9
% 4.28/1.74  
% 4.28/1.74  #Partial instantiations: 0
% 4.28/1.74  #Strategies tried      : 1
% 4.28/1.74  
% 4.28/1.74  Timing (in seconds)
% 4.28/1.74  ----------------------
% 4.28/1.74  Preprocessing        : 0.32
% 4.28/1.74  Parsing              : 0.17
% 4.28/1.74  CNF conversion       : 0.02
% 4.28/1.74  Main loop            : 0.65
% 4.28/1.74  Inferencing          : 0.24
% 4.28/1.74  Reduction            : 0.17
% 4.28/1.74  Demodulation         : 0.12
% 4.28/1.74  BG Simplification    : 0.03
% 4.28/1.74  Subsumption          : 0.15
% 4.28/1.74  Abstraction          : 0.03
% 4.28/1.74  MUC search           : 0.00
% 4.28/1.74  Cooper               : 0.00
% 4.28/1.74  Total                : 1.01
% 4.28/1.74  Index Insertion      : 0.00
% 4.28/1.74  Index Deletion       : 0.00
% 4.28/1.74  Index Matching       : 0.00
% 4.28/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
