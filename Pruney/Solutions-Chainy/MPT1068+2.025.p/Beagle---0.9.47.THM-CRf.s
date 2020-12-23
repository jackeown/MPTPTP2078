%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:44 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 225 expanded)
%              Number of leaves         :   37 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 ( 809 expanded)
%              Number of equality atoms :   50 ( 214 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_59,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_71,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_72,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_106,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_109,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_106])).

tff(c_115,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_109])).

tff(c_119,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_62,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_62])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_130,plain,(
    ! [B_65,C_66,A_67] :
      ( k1_funct_1(k5_relat_1(B_65,C_66),A_67) = k1_funct_1(C_66,k1_funct_1(B_65,A_67))
      | ~ r2_hidden(A_67,k1_relat_1(B_65))
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_201,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_funct_1(k5_relat_1(B_82,C_83),A_84) = k1_funct_1(C_83,k1_funct_1(B_82,A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82)
      | v1_xboole_0(k1_relat_1(B_82))
      | ~ m1_subset_1(A_84,k1_relat_1(B_82)) ) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_203,plain,(
    ! [C_83,A_84] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_83),A_84) = k1_funct_1(C_83,k1_funct_1('#skF_4',A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_84,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_201])).

tff(c_205,plain,(
    ! [C_83,A_84] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_83),A_84) = k1_funct_1(C_83,k1_funct_1('#skF_4',A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_84,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_68,c_48,c_203])).

tff(c_206,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_221,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_206,c_4])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_221])).

tff(c_226,plain,(
    ! [C_83,A_84] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_83),A_84) = k1_funct_1(C_83,k1_funct_1('#skF_4',A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ m1_subset_1(A_84,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_139,plain,(
    ! [C_70,E_73,F_71,B_72,D_68,A_69] :
      ( k1_partfun1(A_69,B_72,C_70,D_68,E_73,F_71) = k5_relat_1(E_73,F_71)
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(C_70,D_68)))
      | ~ v1_funct_1(F_71)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_69,B_72)))
      | ~ v1_funct_1(E_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_143,plain,(
    ! [A_69,B_72,E_73] :
      ( k1_partfun1(A_69,B_72,'#skF_3','#skF_1',E_73,'#skF_5') = k5_relat_1(E_73,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_69,B_72)))
      | ~ v1_funct_1(E_73) ) ),
    inference(resolution,[status(thm)],[c_40,c_139])).

tff(c_159,plain,(
    ! [A_76,B_77,E_78] :
      ( k1_partfun1(A_76,B_77,'#skF_3','#skF_1',E_78,'#skF_5') = k5_relat_1(E_78,'#skF_5')
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(E_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_143])).

tff(c_162,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_168,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_162])).

tff(c_80,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_36,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_85,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_36])).

tff(c_245,plain,(
    ! [C_96,D_95,B_92,A_94,E_93] :
      ( k1_partfun1(A_94,B_92,B_92,C_96,D_95,E_93) = k8_funct_2(A_94,B_92,C_96,D_95,E_93)
      | k1_xboole_0 = B_92
      | ~ r1_tarski(k2_relset_1(A_94,B_92,D_95),k1_relset_1(B_92,C_96,E_93))
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(B_92,C_96)))
      | ~ v1_funct_1(E_93)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_92)))
      | ~ v1_funct_2(D_95,A_94,B_92)
      | ~ v1_funct_1(D_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_251,plain,(
    ! [A_94,D_95] :
      ( k1_partfun1(A_94,'#skF_3','#skF_3','#skF_1',D_95,'#skF_5') = k8_funct_2(A_94,'#skF_3','#skF_1',D_95,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_94,'#skF_3',D_95),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_94,'#skF_3')))
      | ~ v1_funct_2(D_95,A_94,'#skF_3')
      | ~ v1_funct_1(D_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_245])).

tff(c_256,plain,(
    ! [A_94,D_95] :
      ( k1_partfun1(A_94,'#skF_3','#skF_3','#skF_1',D_95,'#skF_5') = k8_funct_2(A_94,'#skF_3','#skF_1',D_95,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_94,'#skF_3',D_95),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_94,'#skF_3')))
      | ~ v1_funct_2(D_95,A_94,'#skF_3')
      | ~ v1_funct_1(D_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_251])).

tff(c_258,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_267,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_2])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_267])).

tff(c_273,plain,(
    ! [A_99,D_100] :
      ( k1_partfun1(A_99,'#skF_3','#skF_3','#skF_1',D_100,'#skF_5') = k8_funct_2(A_99,'#skF_3','#skF_1',D_100,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_99,'#skF_3',D_100),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_99,'#skF_3')))
      | ~ v1_funct_2(D_100,A_99,'#skF_3')
      | ~ v1_funct_1(D_100) ) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_276,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_273])).

tff(c_279,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_168,c_276])).

tff(c_32,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_280,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_32])).

tff(c_287,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_280])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_71,c_42,c_287])).

tff(c_295,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_304,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_2])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.39  
% 2.42/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.40  
% 2.42/1.40  %Foreground sorts:
% 2.42/1.40  
% 2.42/1.40  
% 2.42/1.40  %Background operators:
% 2.42/1.40  
% 2.42/1.40  
% 2.42/1.40  %Foreground operators:
% 2.42/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.42/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.42/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.40  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.40  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.42/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.42/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.40  
% 2.77/1.41  tff(f_132, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 2.77/1.41  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.77/1.41  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.77/1.41  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.77/1.41  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.77/1.41  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.77/1.41  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.77/1.41  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.77/1.41  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.77/1.41  tff(f_79, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 2.77/1.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.77/1.41  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.77/1.41  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_59, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.41  tff(c_65, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_59])).
% 2.77/1.41  tff(c_71, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_65])).
% 2.77/1.41  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_72, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.41  tff(c_79, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_72])).
% 2.77/1.41  tff(c_106, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.77/1.41  tff(c_109, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_106])).
% 2.77/1.41  tff(c_115, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_109])).
% 2.77/1.41  tff(c_119, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_115])).
% 2.77/1.41  tff(c_62, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_59])).
% 2.77/1.41  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_62])).
% 2.77/1.41  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.41  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.77/1.41  tff(c_130, plain, (![B_65, C_66, A_67]: (k1_funct_1(k5_relat_1(B_65, C_66), A_67)=k1_funct_1(C_66, k1_funct_1(B_65, A_67)) | ~r2_hidden(A_67, k1_relat_1(B_65)) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.41  tff(c_201, plain, (![B_82, C_83, A_84]: (k1_funct_1(k5_relat_1(B_82, C_83), A_84)=k1_funct_1(C_83, k1_funct_1(B_82, A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82) | v1_xboole_0(k1_relat_1(B_82)) | ~m1_subset_1(A_84, k1_relat_1(B_82)))), inference(resolution, [status(thm)], [c_6, c_130])).
% 2.77/1.41  tff(c_203, plain, (![C_83, A_84]: (k1_funct_1(k5_relat_1('#skF_4', C_83), A_84)=k1_funct_1(C_83, k1_funct_1('#skF_4', A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_84, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_201])).
% 2.77/1.41  tff(c_205, plain, (![C_83, A_84]: (k1_funct_1(k5_relat_1('#skF_4', C_83), A_84)=k1_funct_1(C_83, k1_funct_1('#skF_4', A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_84, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_68, c_48, c_203])).
% 2.77/1.41  tff(c_206, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_205])).
% 2.77/1.41  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.77/1.41  tff(c_221, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_206, c_4])).
% 2.77/1.41  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_221])).
% 2.77/1.41  tff(c_226, plain, (![C_83, A_84]: (k1_funct_1(k5_relat_1('#skF_4', C_83), A_84)=k1_funct_1(C_83, k1_funct_1('#skF_4', A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~m1_subset_1(A_84, '#skF_2'))), inference(splitRight, [status(thm)], [c_205])).
% 2.77/1.41  tff(c_139, plain, (![C_70, E_73, F_71, B_72, D_68, A_69]: (k1_partfun1(A_69, B_72, C_70, D_68, E_73, F_71)=k5_relat_1(E_73, F_71) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(C_70, D_68))) | ~v1_funct_1(F_71) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_69, B_72))) | ~v1_funct_1(E_73))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.77/1.41  tff(c_143, plain, (![A_69, B_72, E_73]: (k1_partfun1(A_69, B_72, '#skF_3', '#skF_1', E_73, '#skF_5')=k5_relat_1(E_73, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_69, B_72))) | ~v1_funct_1(E_73))), inference(resolution, [status(thm)], [c_40, c_139])).
% 2.77/1.42  tff(c_159, plain, (![A_76, B_77, E_78]: (k1_partfun1(A_76, B_77, '#skF_3', '#skF_1', E_78, '#skF_5')=k5_relat_1(E_78, '#skF_5') | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(E_78))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_143])).
% 2.77/1.42  tff(c_162, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_159])).
% 2.77/1.42  tff(c_168, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_162])).
% 2.77/1.42  tff(c_80, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_72])).
% 2.77/1.42  tff(c_36, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.42  tff(c_85, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_36])).
% 2.77/1.42  tff(c_245, plain, (![C_96, D_95, B_92, A_94, E_93]: (k1_partfun1(A_94, B_92, B_92, C_96, D_95, E_93)=k8_funct_2(A_94, B_92, C_96, D_95, E_93) | k1_xboole_0=B_92 | ~r1_tarski(k2_relset_1(A_94, B_92, D_95), k1_relset_1(B_92, C_96, E_93)) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(B_92, C_96))) | ~v1_funct_1(E_93) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_92))) | ~v1_funct_2(D_95, A_94, B_92) | ~v1_funct_1(D_95))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.77/1.42  tff(c_251, plain, (![A_94, D_95]: (k1_partfun1(A_94, '#skF_3', '#skF_3', '#skF_1', D_95, '#skF_5')=k8_funct_2(A_94, '#skF_3', '#skF_1', D_95, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_94, '#skF_3', D_95), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_94, '#skF_3'))) | ~v1_funct_2(D_95, A_94, '#skF_3') | ~v1_funct_1(D_95))), inference(superposition, [status(thm), theory('equality')], [c_80, c_245])).
% 2.77/1.42  tff(c_256, plain, (![A_94, D_95]: (k1_partfun1(A_94, '#skF_3', '#skF_3', '#skF_1', D_95, '#skF_5')=k8_funct_2(A_94, '#skF_3', '#skF_1', D_95, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_94, '#skF_3', D_95), k1_relat_1('#skF_5')) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_94, '#skF_3'))) | ~v1_funct_2(D_95, A_94, '#skF_3') | ~v1_funct_1(D_95))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_251])).
% 2.77/1.42  tff(c_258, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_256])).
% 2.77/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.77/1.42  tff(c_267, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_2])).
% 2.77/1.42  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_267])).
% 2.77/1.42  tff(c_273, plain, (![A_99, D_100]: (k1_partfun1(A_99, '#skF_3', '#skF_3', '#skF_1', D_100, '#skF_5')=k8_funct_2(A_99, '#skF_3', '#skF_1', D_100, '#skF_5') | ~r1_tarski(k2_relset_1(A_99, '#skF_3', D_100), k1_relat_1('#skF_5')) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_99, '#skF_3'))) | ~v1_funct_2(D_100, A_99, '#skF_3') | ~v1_funct_1(D_100))), inference(splitRight, [status(thm)], [c_256])).
% 2.77/1.42  tff(c_276, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_85, c_273])).
% 2.77/1.42  tff(c_279, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_168, c_276])).
% 2.77/1.42  tff(c_32, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.42  tff(c_280, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_32])).
% 2.77/1.42  tff(c_287, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_226, c_280])).
% 2.77/1.42  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_71, c_42, c_287])).
% 2.77/1.42  tff(c_295, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_115])).
% 2.77/1.42  tff(c_304, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_2])).
% 2.77/1.42  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_304])).
% 2.77/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  Inference rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Ref     : 0
% 2.77/1.42  #Sup     : 50
% 2.77/1.42  #Fact    : 0
% 2.77/1.42  #Define  : 0
% 2.77/1.42  #Split   : 5
% 2.77/1.42  #Chain   : 0
% 2.77/1.42  #Close   : 0
% 2.77/1.42  
% 2.77/1.42  Ordering : KBO
% 2.77/1.42  
% 2.77/1.42  Simplification rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Subsume      : 0
% 2.77/1.42  #Demod        : 82
% 2.77/1.42  #Tautology    : 26
% 2.77/1.42  #SimpNegUnit  : 6
% 2.77/1.42  #BackRed      : 22
% 2.77/1.42  
% 2.77/1.42  #Partial instantiations: 0
% 2.77/1.42  #Strategies tried      : 1
% 2.77/1.42  
% 2.77/1.42  Timing (in seconds)
% 2.77/1.42  ----------------------
% 2.77/1.42  Preprocessing        : 0.35
% 2.77/1.42  Parsing              : 0.19
% 2.77/1.42  CNF conversion       : 0.02
% 2.77/1.42  Main loop            : 0.25
% 2.77/1.42  Inferencing          : 0.09
% 2.77/1.42  Reduction            : 0.08
% 2.77/1.42  Demodulation         : 0.06
% 2.77/1.42  BG Simplification    : 0.02
% 2.77/1.42  Subsumption          : 0.04
% 2.77/1.42  Abstraction          : 0.01
% 2.77/1.42  MUC search           : 0.00
% 2.77/1.42  Cooper               : 0.00
% 2.77/1.42  Total                : 0.64
% 2.77/1.42  Index Insertion      : 0.00
% 2.77/1.42  Index Deletion       : 0.00
% 2.77/1.42  Index Matching       : 0.00
% 2.77/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
