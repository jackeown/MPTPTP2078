%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:42 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 223 expanded)
%              Number of leaves         :   38 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  176 ( 797 expanded)
%              Number of equality atoms :   52 ( 218 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_128,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_75,axiom,(
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
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_27,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_72,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_94,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_57,B_56,C_58) = A_57
      | ~ v1_funct_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_100,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_105,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_80,c_100])).

tff(c_106,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_62])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    ! [B_62,C_63,A_64] :
      ( k1_funct_1(k5_relat_1(B_62,C_63),A_64) = k1_funct_1(C_63,k1_funct_1(B_62,A_64))
      | ~ r2_hidden(A_64,k1_relat_1(B_62))
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_202,plain,(
    ! [B_79,C_80,A_81] :
      ( k1_funct_1(k5_relat_1(B_79,C_80),A_81) = k1_funct_1(C_80,k1_funct_1(B_79,A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79)
      | v1_xboole_0(k1_relat_1(B_79))
      | ~ m1_subset_1(A_81,k1_relat_1(B_79)) ) ),
    inference(resolution,[status(thm)],[c_8,c_131])).

tff(c_204,plain,(
    ! [C_80,A_81] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_80),A_81) = k1_funct_1(C_80,k1_funct_1('#skF_4',A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_81,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_202])).

tff(c_206,plain,(
    ! [C_80,A_81] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_80),A_81) = k1_funct_1(C_80,k1_funct_1('#skF_4',A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_81,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_48,c_204])).

tff(c_207,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_207,c_6])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_222])).

tff(c_227,plain,(
    ! [C_80,A_81] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_80),A_81) = k1_funct_1(C_80,k1_funct_1('#skF_4',A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ m1_subset_1(A_81,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_140,plain,(
    ! [A_70,B_68,C_65,F_66,E_67,D_69] :
      ( k1_partfun1(A_70,B_68,C_65,D_69,E_67,F_66) = k5_relat_1(E_67,F_66)
      | ~ m1_subset_1(F_66,k1_zfmisc_1(k2_zfmisc_1(C_65,D_69)))
      | ~ v1_funct_1(F_66)
      | ~ m1_subset_1(E_67,k1_zfmisc_1(k2_zfmisc_1(A_70,B_68)))
      | ~ v1_funct_1(E_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_142,plain,(
    ! [A_70,B_68,E_67] :
      ( k1_partfun1(A_70,B_68,'#skF_3','#skF_1',E_67,'#skF_5') = k5_relat_1(E_67,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_67,k1_zfmisc_1(k2_zfmisc_1(A_70,B_68)))
      | ~ v1_funct_1(E_67) ) ),
    inference(resolution,[status(thm)],[c_40,c_140])).

tff(c_181,plain,(
    ! [A_76,B_77,E_78] :
      ( k1_partfun1(A_76,B_77,'#skF_3','#skF_1',E_78,'#skF_5') = k5_relat_1(E_78,'#skF_5')
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(E_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_142])).

tff(c_187,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_181])).

tff(c_193,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_187])).

tff(c_79,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_36,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_81,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_36])).

tff(c_246,plain,(
    ! [E_90,B_92,D_89,C_91,A_93] :
      ( k1_partfun1(A_93,B_92,B_92,C_91,D_89,E_90) = k8_funct_2(A_93,B_92,C_91,D_89,E_90)
      | k1_xboole_0 = B_92
      | ~ r1_tarski(k2_relset_1(A_93,B_92,D_89),k1_relset_1(B_92,C_91,E_90))
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(B_92,C_91)))
      | ~ v1_funct_1(E_90)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(D_89,A_93,B_92)
      | ~ v1_funct_1(D_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_252,plain,(
    ! [A_93,D_89] :
      ( k1_partfun1(A_93,'#skF_3','#skF_3','#skF_1',D_89,'#skF_5') = k8_funct_2(A_93,'#skF_3','#skF_1',D_89,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_93,'#skF_3',D_89),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_93,'#skF_3')))
      | ~ v1_funct_2(D_89,A_93,'#skF_3')
      | ~ v1_funct_1(D_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_246])).

tff(c_257,plain,(
    ! [A_93,D_89] :
      ( k1_partfun1(A_93,'#skF_3','#skF_3','#skF_1',D_89,'#skF_5') = k8_funct_2(A_93,'#skF_3','#skF_1',D_89,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_93,'#skF_3',D_89),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_93,'#skF_3')))
      | ~ v1_funct_2(D_89,A_93,'#skF_3')
      | ~ v1_funct_1(D_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_252])).

tff(c_259,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_268,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_51])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_268])).

tff(c_275,plain,(
    ! [A_96,D_97] :
      ( k1_partfun1(A_96,'#skF_3','#skF_3','#skF_1',D_97,'#skF_5') = k8_funct_2(A_96,'#skF_3','#skF_1',D_97,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_96,'#skF_3',D_97),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_96,'#skF_3')))
      | ~ v1_funct_2(D_97,A_96,'#skF_3')
      | ~ v1_funct_1(D_97) ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_278,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_275])).

tff(c_281,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_193,c_278])).

tff(c_32,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_282,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_32])).

tff(c_289,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_282])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69,c_42,c_289])).

tff(c_297,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_305,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_51])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:29:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.41/1.32  
% 2.41/1.32  %Foreground sorts:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Background operators:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Foreground operators:
% 2.41/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.41/1.32  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.41/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.41/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.41/1.32  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.41/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.32  
% 2.72/1.34  tff(f_128, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 2.72/1.34  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.72/1.34  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.72/1.34  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.72/1.34  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.72/1.34  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.72/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.72/1.34  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.72/1.34  tff(f_75, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 2.72/1.34  tff(f_26, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 2.72/1.34  tff(f_27, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.72/1.34  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_62, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.34  tff(c_69, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_62])).
% 2.72/1.34  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_72, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.34  tff(c_80, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_72])).
% 2.72/1.34  tff(c_94, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_relset_1(A_57, B_56, C_58)=A_57 | ~v1_funct_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.72/1.34  tff(c_100, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_94])).
% 2.72/1.34  tff(c_105, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_80, c_100])).
% 2.72/1.34  tff(c_106, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_105])).
% 2.72/1.34  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_62])).
% 2.72/1.34  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_8, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.34  tff(c_131, plain, (![B_62, C_63, A_64]: (k1_funct_1(k5_relat_1(B_62, C_63), A_64)=k1_funct_1(C_63, k1_funct_1(B_62, A_64)) | ~r2_hidden(A_64, k1_relat_1(B_62)) | ~v1_funct_1(C_63) | ~v1_relat_1(C_63) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.34  tff(c_202, plain, (![B_79, C_80, A_81]: (k1_funct_1(k5_relat_1(B_79, C_80), A_81)=k1_funct_1(C_80, k1_funct_1(B_79, A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79) | v1_xboole_0(k1_relat_1(B_79)) | ~m1_subset_1(A_81, k1_relat_1(B_79)))), inference(resolution, [status(thm)], [c_8, c_131])).
% 2.72/1.34  tff(c_204, plain, (![C_80, A_81]: (k1_funct_1(k5_relat_1('#skF_4', C_80), A_81)=k1_funct_1(C_80, k1_funct_1('#skF_4', A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_81, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_202])).
% 2.72/1.34  tff(c_206, plain, (![C_80, A_81]: (k1_funct_1(k5_relat_1('#skF_4', C_80), A_81)=k1_funct_1(C_80, k1_funct_1('#skF_4', A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_81, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_48, c_204])).
% 2.72/1.34  tff(c_207, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_206])).
% 2.72/1.34  tff(c_6, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.34  tff(c_222, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_207, c_6])).
% 2.72/1.34  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_222])).
% 2.72/1.34  tff(c_227, plain, (![C_80, A_81]: (k1_funct_1(k5_relat_1('#skF_4', C_80), A_81)=k1_funct_1(C_80, k1_funct_1('#skF_4', A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~m1_subset_1(A_81, '#skF_2'))), inference(splitRight, [status(thm)], [c_206])).
% 2.72/1.34  tff(c_140, plain, (![A_70, B_68, C_65, F_66, E_67, D_69]: (k1_partfun1(A_70, B_68, C_65, D_69, E_67, F_66)=k5_relat_1(E_67, F_66) | ~m1_subset_1(F_66, k1_zfmisc_1(k2_zfmisc_1(C_65, D_69))) | ~v1_funct_1(F_66) | ~m1_subset_1(E_67, k1_zfmisc_1(k2_zfmisc_1(A_70, B_68))) | ~v1_funct_1(E_67))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.72/1.34  tff(c_142, plain, (![A_70, B_68, E_67]: (k1_partfun1(A_70, B_68, '#skF_3', '#skF_1', E_67, '#skF_5')=k5_relat_1(E_67, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_67, k1_zfmisc_1(k2_zfmisc_1(A_70, B_68))) | ~v1_funct_1(E_67))), inference(resolution, [status(thm)], [c_40, c_140])).
% 2.72/1.34  tff(c_181, plain, (![A_76, B_77, E_78]: (k1_partfun1(A_76, B_77, '#skF_3', '#skF_1', E_78, '#skF_5')=k5_relat_1(E_78, '#skF_5') | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(E_78))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_142])).
% 2.72/1.34  tff(c_187, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_181])).
% 2.72/1.34  tff(c_193, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_187])).
% 2.72/1.34  tff(c_79, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_72])).
% 2.72/1.34  tff(c_36, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_81, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_36])).
% 2.72/1.34  tff(c_246, plain, (![E_90, B_92, D_89, C_91, A_93]: (k1_partfun1(A_93, B_92, B_92, C_91, D_89, E_90)=k8_funct_2(A_93, B_92, C_91, D_89, E_90) | k1_xboole_0=B_92 | ~r1_tarski(k2_relset_1(A_93, B_92, D_89), k1_relset_1(B_92, C_91, E_90)) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(B_92, C_91))) | ~v1_funct_1(E_90) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(D_89, A_93, B_92) | ~v1_funct_1(D_89))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.72/1.34  tff(c_252, plain, (![A_93, D_89]: (k1_partfun1(A_93, '#skF_3', '#skF_3', '#skF_1', D_89, '#skF_5')=k8_funct_2(A_93, '#skF_3', '#skF_1', D_89, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_93, '#skF_3', D_89), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_93, '#skF_3'))) | ~v1_funct_2(D_89, A_93, '#skF_3') | ~v1_funct_1(D_89))), inference(superposition, [status(thm), theory('equality')], [c_79, c_246])).
% 2.72/1.34  tff(c_257, plain, (![A_93, D_89]: (k1_partfun1(A_93, '#skF_3', '#skF_3', '#skF_1', D_89, '#skF_5')=k8_funct_2(A_93, '#skF_3', '#skF_1', D_89, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_93, '#skF_3', D_89), k1_relat_1('#skF_5')) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_93, '#skF_3'))) | ~v1_funct_2(D_89, A_93, '#skF_3') | ~v1_funct_1(D_89))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_252])).
% 2.72/1.34  tff(c_259, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_257])).
% 2.72/1.34  tff(c_2, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.72/1.34  tff(c_4, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.34  tff(c_51, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.72/1.34  tff(c_268, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_51])).
% 2.72/1.34  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_268])).
% 2.72/1.34  tff(c_275, plain, (![A_96, D_97]: (k1_partfun1(A_96, '#skF_3', '#skF_3', '#skF_1', D_97, '#skF_5')=k8_funct_2(A_96, '#skF_3', '#skF_1', D_97, '#skF_5') | ~r1_tarski(k2_relset_1(A_96, '#skF_3', D_97), k1_relat_1('#skF_5')) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_96, '#skF_3'))) | ~v1_funct_2(D_97, A_96, '#skF_3') | ~v1_funct_1(D_97))), inference(splitRight, [status(thm)], [c_257])).
% 2.72/1.34  tff(c_278, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_81, c_275])).
% 2.72/1.34  tff(c_281, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_193, c_278])).
% 2.72/1.34  tff(c_32, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.72/1.34  tff(c_282, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_32])).
% 2.72/1.34  tff(c_289, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_227, c_282])).
% 2.72/1.34  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_69, c_42, c_289])).
% 2.72/1.34  tff(c_297, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_105])).
% 2.72/1.34  tff(c_305, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_51])).
% 2.72/1.34  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_305])).
% 2.72/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.34  
% 2.72/1.34  Inference rules
% 2.72/1.34  ----------------------
% 2.72/1.34  #Ref     : 0
% 2.72/1.34  #Sup     : 52
% 2.72/1.34  #Fact    : 0
% 2.72/1.34  #Define  : 0
% 2.72/1.34  #Split   : 5
% 2.72/1.34  #Chain   : 0
% 2.72/1.34  #Close   : 0
% 2.72/1.34  
% 2.72/1.34  Ordering : KBO
% 2.72/1.34  
% 2.72/1.34  Simplification rules
% 2.72/1.34  ----------------------
% 2.72/1.34  #Subsume      : 0
% 2.72/1.34  #Demod        : 82
% 2.72/1.34  #Tautology    : 28
% 2.72/1.34  #SimpNegUnit  : 6
% 2.72/1.34  #BackRed      : 23
% 2.72/1.34  
% 2.72/1.34  #Partial instantiations: 0
% 2.72/1.34  #Strategies tried      : 1
% 2.72/1.34  
% 2.72/1.34  Timing (in seconds)
% 2.72/1.34  ----------------------
% 2.72/1.34  Preprocessing        : 0.33
% 2.72/1.34  Parsing              : 0.17
% 2.72/1.34  CNF conversion       : 0.02
% 2.72/1.34  Main loop            : 0.25
% 2.72/1.34  Inferencing          : 0.09
% 2.72/1.34  Reduction            : 0.08
% 2.72/1.34  Demodulation         : 0.06
% 2.72/1.34  BG Simplification    : 0.02
% 2.72/1.34  Subsumption          : 0.04
% 2.72/1.34  Abstraction          : 0.01
% 2.72/1.34  MUC search           : 0.00
% 2.72/1.34  Cooper               : 0.00
% 2.72/1.34  Total                : 0.62
% 2.72/1.34  Index Insertion      : 0.00
% 2.72/1.34  Index Deletion       : 0.00
% 2.72/1.34  Index Matching       : 0.00
% 2.72/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
