%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:14 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 112 expanded)
%              Number of leaves         :   42 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 207 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_197,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_201,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_197])).

tff(c_322,plain,(
    ! [B_121,A_122,C_123] :
      ( k1_xboole_0 = B_121
      | k1_relset_1(A_122,B_121,C_123) = A_122
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_329,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_322])).

tff(c_333,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_201,c_329])).

tff(c_334,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_123,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_127,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_123])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_246,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(k1_funct_1(B_92,A_93),k2_relat_1(B_92))
      | ~ r2_hidden(A_93,k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_187,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_191,plain,(
    k2_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_187])).

tff(c_206,plain,(
    ! [A_85,B_86,C_87] :
      ( m1_subset_1(k2_relset_1(A_85,B_86,C_87),k1_zfmisc_1(B_86))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_223,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_206])).

tff(c_229,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_223])).

tff(c_32,plain,(
    ! [A_17,C_19,B_18] :
      ( m1_subset_1(A_17,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_232,plain,(
    ! [A_17] :
      ( m1_subset_1(A_17,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_17,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_229,c_32])).

tff(c_250,plain,(
    ! [A_93] :
      ( m1_subset_1(k1_funct_1('#skF_6',A_93),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_93,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_246,c_232])).

tff(c_258,plain,(
    ! [A_94] :
      ( m1_subset_1(k1_funct_1('#skF_6',A_94),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_94,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_66,c_250])).

tff(c_28,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_tarski(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [D_67,B_68,A_69] :
      ( D_67 = B_68
      | D_67 = A_69
      | ~ r2_hidden(D_67,k2_tarski(A_69,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_168,plain,(
    ! [D_70,A_71] :
      ( D_70 = A_71
      | D_70 = A_71
      | ~ r2_hidden(D_70,k1_tarski(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_172,plain,(
    ! [A_71,A_15] :
      ( A_71 = A_15
      | v1_xboole_0(k1_tarski(A_71))
      | ~ m1_subset_1(A_15,k1_tarski(A_71)) ) ),
    inference(resolution,[status(thm)],[c_30,c_168])).

tff(c_178,plain,(
    ! [A_71,A_15] :
      ( A_71 = A_15
      | ~ m1_subset_1(A_15,k1_tarski(A_71)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_172])).

tff(c_262,plain,(
    ! [A_94] :
      ( k1_funct_1('#skF_6',A_94) = '#skF_4'
      | ~ r2_hidden(A_94,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_258,c_178])).

tff(c_347,plain,(
    ! [A_124] :
      ( k1_funct_1('#skF_6',A_124) = '#skF_4'
      | ~ r2_hidden(A_124,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_262])).

tff(c_354,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_347])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_354])).

tff(c_361,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_71,plain,(
    ! [A_45] : k2_tarski(A_45,A_45) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [D_7,B_3] : r2_hidden(D_7,k2_tarski(D_7,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [A_45] : r2_hidden(A_45,k1_tarski(A_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_8])).

tff(c_88,plain,(
    ! [B_47,A_48] :
      ( ~ r1_tarski(B_47,A_48)
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    ! [A_45] : ~ r1_tarski(k1_tarski(A_45),A_45) ),
    inference(resolution,[status(thm)],[c_77,c_88])).

tff(c_382,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_101])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.60/1.34  
% 2.60/1.34  %Foreground sorts:
% 2.60/1.34  
% 2.60/1.34  
% 2.60/1.34  %Background operators:
% 2.60/1.34  
% 2.60/1.34  
% 2.60/1.34  %Foreground operators:
% 2.60/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.60/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.60/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.60/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.60/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.60/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.34  
% 2.60/1.36  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.60/1.36  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.60/1.36  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.60/1.36  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.60/1.36  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.60/1.36  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.60/1.36  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.60/1.36  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.60/1.36  tff(f_57, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.60/1.36  tff(f_45, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.60/1.36  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.60/1.36  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.60/1.36  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.60/1.36  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.60/1.36  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.36  tff(c_58, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.60/1.36  tff(c_60, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.60/1.36  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.60/1.36  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.60/1.36  tff(c_197, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.60/1.36  tff(c_201, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_197])).
% 2.60/1.36  tff(c_322, plain, (![B_121, A_122, C_123]: (k1_xboole_0=B_121 | k1_relset_1(A_122, B_121, C_123)=A_122 | ~v1_funct_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.60/1.36  tff(c_329, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_322])).
% 2.60/1.36  tff(c_333, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_201, c_329])).
% 2.60/1.36  tff(c_334, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_333])).
% 2.60/1.36  tff(c_123, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.60/1.36  tff(c_127, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_123])).
% 2.60/1.36  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.60/1.36  tff(c_246, plain, (![B_92, A_93]: (r2_hidden(k1_funct_1(B_92, A_93), k2_relat_1(B_92)) | ~r2_hidden(A_93, k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.36  tff(c_187, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.60/1.36  tff(c_191, plain, (k2_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_187])).
% 2.60/1.36  tff(c_206, plain, (![A_85, B_86, C_87]: (m1_subset_1(k2_relset_1(A_85, B_86, C_87), k1_zfmisc_1(B_86)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.60/1.36  tff(c_223, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_191, c_206])).
% 2.60/1.36  tff(c_229, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_223])).
% 2.60/1.36  tff(c_32, plain, (![A_17, C_19, B_18]: (m1_subset_1(A_17, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.36  tff(c_232, plain, (![A_17]: (m1_subset_1(A_17, k1_tarski('#skF_4')) | ~r2_hidden(A_17, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_229, c_32])).
% 2.60/1.36  tff(c_250, plain, (![A_93]: (m1_subset_1(k1_funct_1('#skF_6', A_93), k1_tarski('#skF_4')) | ~r2_hidden(A_93, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_246, c_232])).
% 2.60/1.36  tff(c_258, plain, (![A_94]: (m1_subset_1(k1_funct_1('#skF_6', A_94), k1_tarski('#skF_4')) | ~r2_hidden(A_94, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_66, c_250])).
% 2.60/1.36  tff(c_28, plain, (![A_14]: (~v1_xboole_0(k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.36  tff(c_30, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.36  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.36  tff(c_149, plain, (![D_67, B_68, A_69]: (D_67=B_68 | D_67=A_69 | ~r2_hidden(D_67, k2_tarski(A_69, B_68)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.60/1.36  tff(c_168, plain, (![D_70, A_71]: (D_70=A_71 | D_70=A_71 | ~r2_hidden(D_70, k1_tarski(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_149])).
% 2.60/1.36  tff(c_172, plain, (![A_71, A_15]: (A_71=A_15 | v1_xboole_0(k1_tarski(A_71)) | ~m1_subset_1(A_15, k1_tarski(A_71)))), inference(resolution, [status(thm)], [c_30, c_168])).
% 2.60/1.36  tff(c_178, plain, (![A_71, A_15]: (A_71=A_15 | ~m1_subset_1(A_15, k1_tarski(A_71)))), inference(negUnitSimplification, [status(thm)], [c_28, c_172])).
% 2.60/1.36  tff(c_262, plain, (![A_94]: (k1_funct_1('#skF_6', A_94)='#skF_4' | ~r2_hidden(A_94, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_258, c_178])).
% 2.60/1.36  tff(c_347, plain, (![A_124]: (k1_funct_1('#skF_6', A_124)='#skF_4' | ~r2_hidden(A_124, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_262])).
% 2.60/1.36  tff(c_354, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_347])).
% 2.60/1.36  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_354])).
% 2.60/1.36  tff(c_361, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_333])).
% 2.60/1.36  tff(c_71, plain, (![A_45]: (k2_tarski(A_45, A_45)=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.36  tff(c_8, plain, (![D_7, B_3]: (r2_hidden(D_7, k2_tarski(D_7, B_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.60/1.36  tff(c_77, plain, (![A_45]: (r2_hidden(A_45, k1_tarski(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_8])).
% 2.60/1.36  tff(c_88, plain, (![B_47, A_48]: (~r1_tarski(B_47, A_48) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.36  tff(c_101, plain, (![A_45]: (~r1_tarski(k1_tarski(A_45), A_45))), inference(resolution, [status(thm)], [c_77, c_88])).
% 2.60/1.36  tff(c_382, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_361, c_101])).
% 2.60/1.36  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_382])).
% 2.60/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  Inference rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Ref     : 0
% 2.60/1.36  #Sup     : 66
% 2.60/1.36  #Fact    : 0
% 2.60/1.36  #Define  : 0
% 2.60/1.36  #Split   : 4
% 2.60/1.36  #Chain   : 0
% 2.60/1.36  #Close   : 0
% 2.60/1.36  
% 2.60/1.36  Ordering : KBO
% 2.60/1.36  
% 2.60/1.36  Simplification rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Subsume      : 5
% 2.60/1.36  #Demod        : 22
% 2.60/1.36  #Tautology    : 20
% 2.60/1.36  #SimpNegUnit  : 5
% 2.60/1.36  #BackRed      : 12
% 2.60/1.36  
% 2.60/1.36  #Partial instantiations: 0
% 2.60/1.36  #Strategies tried      : 1
% 2.60/1.36  
% 2.60/1.36  Timing (in seconds)
% 2.60/1.36  ----------------------
% 2.60/1.37  Preprocessing        : 0.34
% 2.60/1.37  Parsing              : 0.18
% 2.60/1.37  CNF conversion       : 0.02
% 2.60/1.37  Main loop            : 0.25
% 2.60/1.37  Inferencing          : 0.09
% 2.60/1.37  Reduction            : 0.08
% 2.60/1.37  Demodulation         : 0.05
% 2.60/1.37  BG Simplification    : 0.02
% 2.60/1.37  Subsumption          : 0.04
% 2.60/1.37  Abstraction          : 0.01
% 2.60/1.37  MUC search           : 0.00
% 2.60/1.37  Cooper               : 0.00
% 2.60/1.37  Total                : 0.63
% 2.60/1.37  Index Insertion      : 0.00
% 2.60/1.37  Index Deletion       : 0.00
% 2.60/1.37  Index Matching       : 0.00
% 2.60/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
