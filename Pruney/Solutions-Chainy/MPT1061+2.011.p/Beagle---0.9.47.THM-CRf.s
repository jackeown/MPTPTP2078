%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:38 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 437 expanded)
%              Number of leaves         :   35 ( 161 expanded)
%              Depth                    :   15
%              Number of atoms          :  196 (1414 expanded)
%              Number of equality atoms :   52 ( 200 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_118,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k7_relset_1(A_61,B_62,C_63,D_64) = k9_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,(
    ! [D_64] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_64) = k9_relat_1('#skF_5',D_64) ),
    inference(resolution,[status(thm)],[c_44,c_118])).

tff(c_40,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_122,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_40])).

tff(c_51,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_160,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k2_partfun1(A_74,B_75,C_76,D_77) = k7_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,(
    ! [D_77] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_77) = k7_relat_1('#skF_5',D_77)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_160])).

tff(c_168,plain,(
    ! [D_77] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_77) = k7_relat_1('#skF_5',D_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_164])).

tff(c_208,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( m1_subset_1(k2_partfun1(A_91,B_92,C_93,D_94),k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_241,plain,(
    ! [D_77] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_77),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_208])).

tff(c_283,plain,(
    ! [D_95] : m1_subset_1(k7_relat_1('#skF_5',D_95),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_241])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_312,plain,(
    ! [D_95] : v1_relat_1(k7_relat_1('#skF_5',D_95)) ),
    inference(resolution,[status(thm)],[c_283,c_8])).

tff(c_110,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( v1_funct_1(k2_partfun1(A_56,B_57,C_58,D_59))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_112,plain,(
    ! [D_59] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_59))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_115,plain,(
    ! [D_59] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_112])).

tff(c_169,plain,(
    ! [D_59] : v1_funct_1(k7_relat_1('#skF_5',D_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_115])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_99,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_103,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_99])).

tff(c_196,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,C_90) = A_89
      | ~ v1_funct_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_202,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_196])).

tff(c_206,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_103,c_202])).

tff(c_207,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_relat_1(k7_relat_1(B_4,A_3)) = A_3
      | ~ r1_tarski(A_3,k1_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_267,plain,(
    ! [A_3] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_3)) = A_3
      | ~ r1_tarski(A_3,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_6])).

tff(c_315,plain,(
    ! [A_98] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_98)) = A_98
      | ~ r1_tarski(A_98,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_267])).

tff(c_32,plain,(
    ! [B_27,A_26] :
      ( m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_27),A_26)))
      | ~ r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_324,plain,(
    ! [A_98,A_26] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_98),k1_zfmisc_1(k2_zfmisc_1(A_98,A_26)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_98)),A_26)
      | ~ v1_funct_1(k7_relat_1('#skF_5',A_98))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_98))
      | ~ r1_tarski(A_98,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_32])).

tff(c_628,plain,(
    ! [A_161,A_162] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_161),k1_zfmisc_1(k2_zfmisc_1(A_161,A_162)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_161)),A_162)
      | ~ r1_tarski(A_161,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_169,c_324])).

tff(c_78,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( v1_funct_1(k2_partfun1(A_42,B_43,C_44,D_45))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_80,plain,(
    ! [D_45] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_45))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_83,plain,(
    ! [D_45] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_38,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56])).

tff(c_87,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_181,plain,
    ( ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_168,c_87])).

tff(c_182,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_639,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_628,c_182])).

tff(c_671,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_639])).

tff(c_687,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_671])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_122,c_687])).

tff(c_691,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_699,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_2])).

tff(c_701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_699])).

tff(c_703,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_724,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_703,c_8])).

tff(c_771,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_780,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_771])).

tff(c_787,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_103,c_780])).

tff(c_788,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_787])).

tff(c_802,plain,(
    ! [A_3] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_3)) = A_3
      | ~ r1_tarski(A_3,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_6])).

tff(c_819,plain,(
    ! [A_176] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_176)) = A_176
      | ~ r1_tarski(A_176,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_802])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_723,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_703,c_10])).

tff(c_702,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_725,plain,(
    ! [B_163,C_164,A_165] :
      ( k1_xboole_0 = B_163
      | v1_funct_2(C_164,A_165,B_163)
      | k1_relset_1(A_165,B_163,C_164) != A_165
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_728,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_703,c_725])).

tff(c_737,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_702,c_728])).

tff(c_742,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_737])).

tff(c_743,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_742])).

tff(c_825,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_743])).

tff(c_845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_825])).

tff(c_846,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_787])).

tff(c_854,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_2])).

tff(c_856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_854])).

tff(c_858,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_920,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_723])).

tff(c_34,plain,(
    ! [B_27,A_26] :
      ( v1_funct_2(B_27,k1_relat_1(B_27),A_26)
      | ~ r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_930,plain,(
    ! [A_26] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_26)
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),A_26)
      | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_34])).

tff(c_1206,plain,(
    ! [A_216] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_216)
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_169,c_930])).

tff(c_1209,plain,(
    ! [A_216] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_216)
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),A_216)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1206])).

tff(c_1215,plain,(
    ! [A_219] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_219)
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1209])).

tff(c_1218,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1215,c_702])).

tff(c_1222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:11:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.63  
% 3.58/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.63  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.58/1.63  
% 3.58/1.63  %Foreground sorts:
% 3.58/1.63  
% 3.58/1.63  
% 3.58/1.63  %Background operators:
% 3.58/1.63  
% 3.58/1.63  
% 3.58/1.63  %Foreground operators:
% 3.58/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.58/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.58/1.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.58/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.58/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.58/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.63  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.58/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.58/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.63  
% 3.72/1.65  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 3.72/1.65  tff(f_48, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.72/1.65  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.72/1.65  tff(f_30, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.72/1.65  tff(f_80, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.72/1.65  tff(f_74, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.72/1.65  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.72/1.65  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.72/1.65  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.72/1.65  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.72/1.65  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.72/1.65  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.72/1.65  tff(c_118, plain, (![A_61, B_62, C_63, D_64]: (k7_relset_1(A_61, B_62, C_63, D_64)=k9_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.72/1.65  tff(c_121, plain, (![D_64]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_64)=k9_relat_1('#skF_5', D_64))), inference(resolution, [status(thm)], [c_44, c_118])).
% 3.72/1.65  tff(c_40, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.72/1.65  tff(c_122, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_40])).
% 3.72/1.65  tff(c_51, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.72/1.65  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_51])).
% 3.72/1.65  tff(c_4, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.72/1.65  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.72/1.65  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.72/1.65  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.72/1.65  tff(c_160, plain, (![A_74, B_75, C_76, D_77]: (k2_partfun1(A_74, B_75, C_76, D_77)=k7_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.72/1.65  tff(c_164, plain, (![D_77]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_77)=k7_relat_1('#skF_5', D_77) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_160])).
% 3.72/1.65  tff(c_168, plain, (![D_77]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_77)=k7_relat_1('#skF_5', D_77))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_164])).
% 3.72/1.65  tff(c_208, plain, (![A_91, B_92, C_93, D_94]: (m1_subset_1(k2_partfun1(A_91, B_92, C_93, D_94), k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.72/1.65  tff(c_241, plain, (![D_77]: (m1_subset_1(k7_relat_1('#skF_5', D_77), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_208])).
% 3.72/1.65  tff(c_283, plain, (![D_95]: (m1_subset_1(k7_relat_1('#skF_5', D_95), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_241])).
% 3.72/1.65  tff(c_8, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.72/1.65  tff(c_312, plain, (![D_95]: (v1_relat_1(k7_relat_1('#skF_5', D_95)))), inference(resolution, [status(thm)], [c_283, c_8])).
% 3.72/1.65  tff(c_110, plain, (![A_56, B_57, C_58, D_59]: (v1_funct_1(k2_partfun1(A_56, B_57, C_58, D_59)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.72/1.65  tff(c_112, plain, (![D_59]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_59)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_110])).
% 3.72/1.65  tff(c_115, plain, (![D_59]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_59)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_112])).
% 3.72/1.65  tff(c_169, plain, (![D_59]: (v1_funct_1(k7_relat_1('#skF_5', D_59)))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_115])).
% 3.72/1.65  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.72/1.65  tff(c_99, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.72/1.65  tff(c_103, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_99])).
% 3.72/1.65  tff(c_196, plain, (![B_88, A_89, C_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, C_90)=A_89 | ~v1_funct_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.72/1.65  tff(c_202, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_196])).
% 3.72/1.65  tff(c_206, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_103, c_202])).
% 3.72/1.65  tff(c_207, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_206])).
% 3.72/1.65  tff(c_6, plain, (![B_4, A_3]: (k1_relat_1(k7_relat_1(B_4, A_3))=A_3 | ~r1_tarski(A_3, k1_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.72/1.65  tff(c_267, plain, (![A_3]: (k1_relat_1(k7_relat_1('#skF_5', A_3))=A_3 | ~r1_tarski(A_3, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_6])).
% 3.72/1.65  tff(c_315, plain, (![A_98]: (k1_relat_1(k7_relat_1('#skF_5', A_98))=A_98 | ~r1_tarski(A_98, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_267])).
% 3.72/1.65  tff(c_32, plain, (![B_27, A_26]: (m1_subset_1(B_27, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_27), A_26))) | ~r1_tarski(k2_relat_1(B_27), A_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.72/1.65  tff(c_324, plain, (![A_98, A_26]: (m1_subset_1(k7_relat_1('#skF_5', A_98), k1_zfmisc_1(k2_zfmisc_1(A_98, A_26))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_98)), A_26) | ~v1_funct_1(k7_relat_1('#skF_5', A_98)) | ~v1_relat_1(k7_relat_1('#skF_5', A_98)) | ~r1_tarski(A_98, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_315, c_32])).
% 3.72/1.65  tff(c_628, plain, (![A_161, A_162]: (m1_subset_1(k7_relat_1('#skF_5', A_161), k1_zfmisc_1(k2_zfmisc_1(A_161, A_162))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_161)), A_162) | ~r1_tarski(A_161, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_169, c_324])).
% 3.72/1.65  tff(c_78, plain, (![A_42, B_43, C_44, D_45]: (v1_funct_1(k2_partfun1(A_42, B_43, C_44, D_45)) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.72/1.65  tff(c_80, plain, (![D_45]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_45)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_78])).
% 3.72/1.65  tff(c_83, plain, (![D_45]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_45)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80])).
% 3.72/1.65  tff(c_38, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.72/1.65  tff(c_56, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 3.72/1.65  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56])).
% 3.72/1.65  tff(c_87, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_38])).
% 3.72/1.65  tff(c_181, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_168, c_87])).
% 3.72/1.65  tff(c_182, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_181])).
% 3.72/1.65  tff(c_639, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_628, c_182])).
% 3.72/1.65  tff(c_671, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_639])).
% 3.72/1.65  tff(c_687, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4, c_671])).
% 3.72/1.65  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_122, c_687])).
% 3.72/1.65  tff(c_691, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_206])).
% 3.72/1.65  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.72/1.65  tff(c_699, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_691, c_2])).
% 3.72/1.65  tff(c_701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_699])).
% 3.72/1.65  tff(c_703, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_181])).
% 3.72/1.65  tff(c_724, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_703, c_8])).
% 3.72/1.65  tff(c_771, plain, (![B_172, A_173, C_174]: (k1_xboole_0=B_172 | k1_relset_1(A_173, B_172, C_174)=A_173 | ~v1_funct_2(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.72/1.65  tff(c_780, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_771])).
% 3.72/1.65  tff(c_787, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_103, c_780])).
% 3.72/1.65  tff(c_788, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_787])).
% 3.72/1.65  tff(c_802, plain, (![A_3]: (k1_relat_1(k7_relat_1('#skF_5', A_3))=A_3 | ~r1_tarski(A_3, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_788, c_6])).
% 3.72/1.65  tff(c_819, plain, (![A_176]: (k1_relat_1(k7_relat_1('#skF_5', A_176))=A_176 | ~r1_tarski(A_176, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_802])).
% 3.72/1.65  tff(c_10, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.72/1.65  tff(c_723, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_703, c_10])).
% 3.72/1.65  tff(c_702, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_181])).
% 3.72/1.65  tff(c_725, plain, (![B_163, C_164, A_165]: (k1_xboole_0=B_163 | v1_funct_2(C_164, A_165, B_163) | k1_relset_1(A_165, B_163, C_164)!=A_165 | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_163))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.72/1.65  tff(c_728, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_703, c_725])).
% 3.72/1.65  tff(c_737, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_702, c_728])).
% 3.72/1.65  tff(c_742, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_737])).
% 3.72/1.65  tff(c_743, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_723, c_742])).
% 3.72/1.65  tff(c_825, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_819, c_743])).
% 3.72/1.65  tff(c_845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_825])).
% 3.72/1.65  tff(c_846, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_787])).
% 3.72/1.65  tff(c_854, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_846, c_2])).
% 3.72/1.65  tff(c_856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_854])).
% 3.72/1.65  tff(c_858, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_737])).
% 3.72/1.65  tff(c_920, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_858, c_723])).
% 3.72/1.65  tff(c_34, plain, (![B_27, A_26]: (v1_funct_2(B_27, k1_relat_1(B_27), A_26) | ~r1_tarski(k2_relat_1(B_27), A_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.72/1.65  tff(c_930, plain, (![A_26]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_26) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), A_26) | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_920, c_34])).
% 3.72/1.65  tff(c_1206, plain, (![A_216]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_216) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), A_216))), inference(demodulation, [status(thm), theory('equality')], [c_724, c_169, c_930])).
% 3.72/1.65  tff(c_1209, plain, (![A_216]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_216) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), A_216) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1206])).
% 3.72/1.65  tff(c_1215, plain, (![A_219]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_219) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), A_219))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1209])).
% 3.72/1.65  tff(c_1218, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1215, c_702])).
% 3.72/1.65  tff(c_1222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_1218])).
% 3.72/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.65  
% 3.72/1.65  Inference rules
% 3.72/1.65  ----------------------
% 3.72/1.65  #Ref     : 0
% 3.72/1.65  #Sup     : 243
% 3.72/1.65  #Fact    : 0
% 3.72/1.65  #Define  : 0
% 3.72/1.65  #Split   : 8
% 3.72/1.65  #Chain   : 0
% 3.72/1.65  #Close   : 0
% 3.72/1.65  
% 3.72/1.65  Ordering : KBO
% 3.72/1.65  
% 3.72/1.65  Simplification rules
% 3.72/1.65  ----------------------
% 3.72/1.65  #Subsume      : 18
% 3.72/1.65  #Demod        : 230
% 3.72/1.65  #Tautology    : 82
% 3.72/1.65  #SimpNegUnit  : 6
% 3.72/1.65  #BackRed      : 40
% 3.72/1.65  
% 3.72/1.65  #Partial instantiations: 0
% 3.72/1.65  #Strategies tried      : 1
% 3.72/1.65  
% 3.72/1.65  Timing (in seconds)
% 3.72/1.65  ----------------------
% 3.72/1.66  Preprocessing        : 0.35
% 3.72/1.66  Parsing              : 0.19
% 3.72/1.66  CNF conversion       : 0.02
% 3.72/1.66  Main loop            : 0.47
% 3.72/1.66  Inferencing          : 0.18
% 3.72/1.66  Reduction            : 0.15
% 3.72/1.66  Demodulation         : 0.11
% 3.72/1.66  BG Simplification    : 0.03
% 3.72/1.66  Subsumption          : 0.07
% 3.72/1.66  Abstraction          : 0.03
% 3.72/1.66  MUC search           : 0.00
% 3.72/1.66  Cooper               : 0.00
% 3.72/1.66  Total                : 0.87
% 3.72/1.66  Index Insertion      : 0.00
% 3.72/1.66  Index Deletion       : 0.00
% 3.72/1.66  Index Matching       : 0.00
% 3.72/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
