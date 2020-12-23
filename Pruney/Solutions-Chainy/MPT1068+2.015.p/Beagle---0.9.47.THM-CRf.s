%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:42 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 216 expanded)
%              Number of leaves         :   36 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 791 expanded)
%              Number of equality atoms :   50 ( 214 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_127,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_55,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_98,plain,(
    ! [B_59,A_60,C_61] :
      ( k1_xboole_0 = B_59
      | k1_relset_1(A_60,B_59,C_61) = A_60
      | ~ v1_funct_2(C_61,A_60,B_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_107,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_73,c_101])).

tff(c_110,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_62,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_55])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_123,plain,(
    ! [B_62,C_63,A_64] :
      ( k1_funct_1(k5_relat_1(B_62,C_63),A_64) = k1_funct_1(C_63,k1_funct_1(B_62,A_64))
      | ~ r2_hidden(A_64,k1_relat_1(B_62))
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_194,plain,(
    ! [B_79,C_80,A_81] :
      ( k1_funct_1(k5_relat_1(B_79,C_80),A_81) = k1_funct_1(C_80,k1_funct_1(B_79,A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79)
      | v1_xboole_0(k1_relat_1(B_79))
      | ~ m1_subset_1(A_81,k1_relat_1(B_79)) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_196,plain,(
    ! [C_80,A_81] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_80),A_81) = k1_funct_1(C_80,k1_funct_1('#skF_4',A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_81,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_194])).

tff(c_198,plain,(
    ! [C_80,A_81] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_80),A_81) = k1_funct_1(C_80,k1_funct_1('#skF_4',A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_81,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_62,c_46,c_196])).

tff(c_199,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_202,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_202])).

tff(c_207,plain,(
    ! [C_80,A_81] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_80),A_81) = k1_funct_1(C_80,k1_funct_1('#skF_4',A_81))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ m1_subset_1(A_81,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_141,plain,(
    ! [B_70,F_68,C_67,A_72,E_69,D_71] :
      ( k1_partfun1(A_72,B_70,C_67,D_71,E_69,F_68) = k5_relat_1(E_69,F_68)
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_67,D_71)))
      | ~ v1_funct_1(F_68)
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_72,B_70)))
      | ~ v1_funct_1(E_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_145,plain,(
    ! [A_72,B_70,E_69] :
      ( k1_partfun1(A_72,B_70,'#skF_3','#skF_1',E_69,'#skF_5') = k5_relat_1(E_69,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_72,B_70)))
      | ~ v1_funct_1(E_69) ) ),
    inference(resolution,[status(thm)],[c_38,c_141])).

tff(c_173,plain,(
    ! [A_76,B_77,E_78] :
      ( k1_partfun1(A_76,B_77,'#skF_3','#skF_1',E_78,'#skF_5') = k5_relat_1(E_78,'#skF_5')
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(E_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_145])).

tff(c_176,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_182,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_176])).

tff(c_74,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_79,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34])).

tff(c_209,plain,(
    ! [E_83,C_84,B_85,D_82,A_86] :
      ( k1_partfun1(A_86,B_85,B_85,C_84,D_82,E_83) = k8_funct_2(A_86,B_85,C_84,D_82,E_83)
      | k1_xboole_0 = B_85
      | ~ r1_tarski(k2_relset_1(A_86,B_85,D_82),k1_relset_1(B_85,C_84,E_83))
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(B_85,C_84)))
      | ~ v1_funct_1(E_83)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85)))
      | ~ v1_funct_2(D_82,A_86,B_85)
      | ~ v1_funct_1(D_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_215,plain,(
    ! [A_86,D_82] :
      ( k1_partfun1(A_86,'#skF_3','#skF_3','#skF_1',D_82,'#skF_5') = k8_funct_2(A_86,'#skF_3','#skF_1',D_82,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_86,'#skF_3',D_82),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_86,'#skF_3')))
      | ~ v1_funct_2(D_82,A_86,'#skF_3')
      | ~ v1_funct_1(D_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_209])).

tff(c_220,plain,(
    ! [A_86,D_82] :
      ( k1_partfun1(A_86,'#skF_3','#skF_3','#skF_1',D_82,'#skF_5') = k8_funct_2(A_86,'#skF_3','#skF_1',D_82,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_86,'#skF_3',D_82),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_86,'#skF_3')))
      | ~ v1_funct_2(D_82,A_86,'#skF_3')
      | ~ v1_funct_1(D_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_215])).

tff(c_239,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_248,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_2])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_248])).

tff(c_254,plain,(
    ! [A_91,D_92] :
      ( k1_partfun1(A_91,'#skF_3','#skF_3','#skF_1',D_92,'#skF_5') = k8_funct_2(A_91,'#skF_3','#skF_1',D_92,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_91,'#skF_3',D_92),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_91,'#skF_3')))
      | ~ v1_funct_2(D_92,A_91,'#skF_3')
      | ~ v1_funct_1(D_92) ) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_257,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_254])).

tff(c_260,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_182,c_257])).

tff(c_30,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_261,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_30])).

tff(c_268,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_261])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_63,c_40,c_268])).

tff(c_276,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_290,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_2])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n002.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 09:39:21 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.49/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.49/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.35  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.35  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.49/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.35  
% 2.49/1.37  tff(f_127, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.49/1.37  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.49/1.37  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.49/1.37  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.49/1.37  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.49/1.37  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.49/1.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.49/1.37  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.49/1.37  tff(f_74, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.49/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.49/1.37  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_55, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.37  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_55])).
% 2.49/1.37  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_66, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.49/1.37  tff(c_73, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_66])).
% 2.49/1.37  tff(c_98, plain, (![B_59, A_60, C_61]: (k1_xboole_0=B_59 | k1_relset_1(A_60, B_59, C_61)=A_60 | ~v1_funct_2(C_61, A_60, B_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.37  tff(c_101, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_98])).
% 2.49/1.37  tff(c_107, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_73, c_101])).
% 2.49/1.37  tff(c_110, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_107])).
% 2.49/1.37  tff(c_62, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_55])).
% 2.49/1.37  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.37  tff(c_123, plain, (![B_62, C_63, A_64]: (k1_funct_1(k5_relat_1(B_62, C_63), A_64)=k1_funct_1(C_63, k1_funct_1(B_62, A_64)) | ~r2_hidden(A_64, k1_relat_1(B_62)) | ~v1_funct_1(C_63) | ~v1_relat_1(C_63) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.49/1.37  tff(c_194, plain, (![B_79, C_80, A_81]: (k1_funct_1(k5_relat_1(B_79, C_80), A_81)=k1_funct_1(C_80, k1_funct_1(B_79, A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79) | v1_xboole_0(k1_relat_1(B_79)) | ~m1_subset_1(A_81, k1_relat_1(B_79)))), inference(resolution, [status(thm)], [c_6, c_123])).
% 2.49/1.37  tff(c_196, plain, (![C_80, A_81]: (k1_funct_1(k5_relat_1('#skF_4', C_80), A_81)=k1_funct_1(C_80, k1_funct_1('#skF_4', A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_81, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_194])).
% 2.49/1.37  tff(c_198, plain, (![C_80, A_81]: (k1_funct_1(k5_relat_1('#skF_4', C_80), A_81)=k1_funct_1(C_80, k1_funct_1('#skF_4', A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_81, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_62, c_46, c_196])).
% 2.49/1.37  tff(c_199, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_198])).
% 2.49/1.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.49/1.37  tff(c_202, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_199, c_4])).
% 2.49/1.37  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_202])).
% 2.49/1.37  tff(c_207, plain, (![C_80, A_81]: (k1_funct_1(k5_relat_1('#skF_4', C_80), A_81)=k1_funct_1(C_80, k1_funct_1('#skF_4', A_81)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~m1_subset_1(A_81, '#skF_2'))), inference(splitRight, [status(thm)], [c_198])).
% 2.49/1.37  tff(c_141, plain, (![B_70, F_68, C_67, A_72, E_69, D_71]: (k1_partfun1(A_72, B_70, C_67, D_71, E_69, F_68)=k5_relat_1(E_69, F_68) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_67, D_71))) | ~v1_funct_1(F_68) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_72, B_70))) | ~v1_funct_1(E_69))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.49/1.37  tff(c_145, plain, (![A_72, B_70, E_69]: (k1_partfun1(A_72, B_70, '#skF_3', '#skF_1', E_69, '#skF_5')=k5_relat_1(E_69, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_72, B_70))) | ~v1_funct_1(E_69))), inference(resolution, [status(thm)], [c_38, c_141])).
% 2.49/1.37  tff(c_173, plain, (![A_76, B_77, E_78]: (k1_partfun1(A_76, B_77, '#skF_3', '#skF_1', E_78, '#skF_5')=k5_relat_1(E_78, '#skF_5') | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(E_78))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_145])).
% 2.49/1.37  tff(c_176, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_173])).
% 2.49/1.37  tff(c_182, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_176])).
% 2.49/1.37  tff(c_74, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_66])).
% 2.49/1.37  tff(c_34, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_79, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_34])).
% 2.49/1.37  tff(c_209, plain, (![E_83, C_84, B_85, D_82, A_86]: (k1_partfun1(A_86, B_85, B_85, C_84, D_82, E_83)=k8_funct_2(A_86, B_85, C_84, D_82, E_83) | k1_xboole_0=B_85 | ~r1_tarski(k2_relset_1(A_86, B_85, D_82), k1_relset_1(B_85, C_84, E_83)) | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(B_85, C_84))) | ~v1_funct_1(E_83) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))) | ~v1_funct_2(D_82, A_86, B_85) | ~v1_funct_1(D_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.37  tff(c_215, plain, (![A_86, D_82]: (k1_partfun1(A_86, '#skF_3', '#skF_3', '#skF_1', D_82, '#skF_5')=k8_funct_2(A_86, '#skF_3', '#skF_1', D_82, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_86, '#skF_3', D_82), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_86, '#skF_3'))) | ~v1_funct_2(D_82, A_86, '#skF_3') | ~v1_funct_1(D_82))), inference(superposition, [status(thm), theory('equality')], [c_74, c_209])).
% 2.49/1.37  tff(c_220, plain, (![A_86, D_82]: (k1_partfun1(A_86, '#skF_3', '#skF_3', '#skF_1', D_82, '#skF_5')=k8_funct_2(A_86, '#skF_3', '#skF_1', D_82, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_86, '#skF_3', D_82), k1_relat_1('#skF_5')) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_86, '#skF_3'))) | ~v1_funct_2(D_82, A_86, '#skF_3') | ~v1_funct_1(D_82))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_215])).
% 2.49/1.37  tff(c_239, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_220])).
% 2.49/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.49/1.37  tff(c_248, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_2])).
% 2.49/1.37  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_248])).
% 2.49/1.37  tff(c_254, plain, (![A_91, D_92]: (k1_partfun1(A_91, '#skF_3', '#skF_3', '#skF_1', D_92, '#skF_5')=k8_funct_2(A_91, '#skF_3', '#skF_1', D_92, '#skF_5') | ~r1_tarski(k2_relset_1(A_91, '#skF_3', D_92), k1_relat_1('#skF_5')) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_91, '#skF_3'))) | ~v1_funct_2(D_92, A_91, '#skF_3') | ~v1_funct_1(D_92))), inference(splitRight, [status(thm)], [c_220])).
% 2.49/1.37  tff(c_257, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_79, c_254])).
% 2.49/1.37  tff(c_260, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_182, c_257])).
% 2.49/1.37  tff(c_30, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.49/1.37  tff(c_261, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_30])).
% 2.49/1.37  tff(c_268, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_261])).
% 2.49/1.37  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_63, c_40, c_268])).
% 2.49/1.37  tff(c_276, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_107])).
% 2.49/1.37  tff(c_290, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_2])).
% 2.49/1.37  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_290])).
% 2.49/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.37  
% 2.49/1.37  Inference rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Ref     : 0
% 2.49/1.37  #Sup     : 49
% 2.49/1.37  #Fact    : 0
% 2.49/1.37  #Define  : 0
% 2.49/1.37  #Split   : 5
% 2.49/1.37  #Chain   : 0
% 2.49/1.37  #Close   : 0
% 2.49/1.37  
% 2.49/1.37  Ordering : KBO
% 2.49/1.37  
% 2.49/1.37  Simplification rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Subsume      : 0
% 2.49/1.37  #Demod        : 76
% 2.49/1.37  #Tautology    : 26
% 2.49/1.37  #SimpNegUnit  : 5
% 2.49/1.37  #BackRed      : 22
% 2.49/1.37  
% 2.49/1.37  #Partial instantiations: 0
% 2.49/1.37  #Strategies tried      : 1
% 2.49/1.37  
% 2.49/1.37  Timing (in seconds)
% 2.49/1.37  ----------------------
% 2.49/1.37  Preprocessing        : 0.39
% 2.49/1.37  Parsing              : 0.20
% 2.49/1.37  CNF conversion       : 0.03
% 2.49/1.37  Main loop            : 0.24
% 2.49/1.37  Inferencing          : 0.08
% 2.49/1.37  Reduction            : 0.08
% 2.49/1.37  Demodulation         : 0.05
% 2.49/1.37  BG Simplification    : 0.02
% 2.49/1.37  Subsumption          : 0.04
% 2.49/1.37  Abstraction          : 0.01
% 2.49/1.37  MUC search           : 0.00
% 2.49/1.37  Cooper               : 0.00
% 2.49/1.37  Total                : 0.66
% 2.49/1.37  Index Insertion      : 0.00
% 2.49/1.37  Index Deletion       : 0.00
% 2.49/1.37  Index Matching       : 0.00
% 2.49/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
