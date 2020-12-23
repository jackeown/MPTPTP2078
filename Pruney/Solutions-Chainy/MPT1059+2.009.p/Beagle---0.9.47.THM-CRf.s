%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:34 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 105 expanded)
%              Number of leaves         :   34 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 271 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k9_setfam_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_27,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_107,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_107])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_126,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_126])).

tff(c_158,plain,(
    ! [B_65,A_66,C_67] :
      ( k1_xboole_0 = B_65
      | k1_relset_1(A_66,B_65,C_67) = A_66
      | ~ v1_funct_2(C_67,A_66,B_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_165,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_158])).

tff(c_169,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_135,c_165])).

tff(c_170,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_191,plain,(
    ! [A_71,B_72,C_73] :
      ( k7_partfun1(A_71,B_72,C_73) = k1_funct_1(B_72,C_73)
      | ~ r2_hidden(C_73,k1_relat_1(B_72))
      | ~ v1_funct_1(B_72)
      | ~ v5_relat_1(B_72,A_71)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_193,plain,(
    ! [A_71,C_73] :
      ( k7_partfun1(A_71,'#skF_3',C_73) = k1_funct_1('#skF_3',C_73)
      | ~ r2_hidden(C_73,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_71)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_191])).

tff(c_200,plain,(
    ! [A_74,C_75] :
      ( k7_partfun1(A_74,'#skF_3',C_75) = k1_funct_1('#skF_3',C_75)
      | ~ r2_hidden(C_75,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_48,c_193])).

tff(c_203,plain,(
    ! [A_74,B_2] :
      ( k7_partfun1(A_74,'#skF_3',B_2) = k1_funct_1('#skF_3',B_2)
      | ~ v5_relat_1('#skF_3',A_74)
      | ~ m1_subset_1(B_2,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_200])).

tff(c_207,plain,(
    ! [A_76,B_77] :
      ( k7_partfun1(A_76,'#skF_3',B_77) = k1_funct_1('#skF_3',B_77)
      | ~ v5_relat_1('#skF_3',A_76)
      | ~ m1_subset_1(B_77,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_203])).

tff(c_211,plain,(
    ! [B_78] :
      ( k7_partfun1('#skF_2','#skF_3',B_78) = k1_funct_1('#skF_3',B_78)
      | ~ m1_subset_1(B_78,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_116,c_207])).

tff(c_220,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_211])).

tff(c_40,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_221,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_40])).

tff(c_233,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k3_funct_2(A_82,B_83,C_84,D_85) = k1_funct_1(C_84,D_85)
      | ~ m1_subset_1(D_85,A_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(C_84,A_82,B_83)
      | ~ v1_funct_1(C_84)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_239,plain,(
    ! [B_83,C_84] :
      ( k3_funct_2('#skF_1',B_83,C_84,'#skF_4') = k1_funct_1(C_84,'#skF_4')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_83)))
      | ~ v1_funct_2(C_84,'#skF_1',B_83)
      | ~ v1_funct_1(C_84)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_233])).

tff(c_247,plain,(
    ! [B_86,C_87] :
      ( k3_funct_2('#skF_1',B_86,C_87,'#skF_4') = k1_funct_1(C_87,'#skF_4')
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_86)))
      | ~ v1_funct_2(C_87,'#skF_1',B_86)
      | ~ v1_funct_1(C_87) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_239])).

tff(c_254,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_247])).

tff(c_258,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_254])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_258])).

tff(c_261,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_269,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_4])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.27  
% 2.33/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k9_setfam_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.33/1.28  
% 2.33/1.28  %Foreground sorts:
% 2.33/1.28  
% 2.33/1.28  
% 2.33/1.28  %Background operators:
% 2.33/1.28  
% 2.33/1.28  
% 2.33/1.28  %Foreground operators:
% 2.33/1.28  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.33/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.28  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.33/1.28  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.33/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.33/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.33/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.33/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.33/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.33/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.28  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.33/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.28  
% 2.33/1.29  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.33/1.29  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.33/1.29  tff(f_40, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.33/1.29  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.33/1.29  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.33/1.29  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.33/1.29  tff(f_83, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.33/1.29  tff(f_96, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.33/1.29  tff(f_27, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.33/1.29  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.33/1.29  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.33/1.29  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.33/1.29  tff(c_107, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.29  tff(c_116, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_107])).
% 2.33/1.29  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.33/1.29  tff(c_8, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.33/1.29  tff(c_81, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.33/1.29  tff(c_90, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_81])).
% 2.33/1.29  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.33/1.29  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.33/1.29  tff(c_126, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.29  tff(c_135, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_126])).
% 2.33/1.29  tff(c_158, plain, (![B_65, A_66, C_67]: (k1_xboole_0=B_65 | k1_relset_1(A_66, B_65, C_67)=A_66 | ~v1_funct_2(C_67, A_66, B_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.33/1.29  tff(c_165, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_158])).
% 2.33/1.29  tff(c_169, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_135, c_165])).
% 2.33/1.29  tff(c_170, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_169])).
% 2.33/1.29  tff(c_191, plain, (![A_71, B_72, C_73]: (k7_partfun1(A_71, B_72, C_73)=k1_funct_1(B_72, C_73) | ~r2_hidden(C_73, k1_relat_1(B_72)) | ~v1_funct_1(B_72) | ~v5_relat_1(B_72, A_71) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.33/1.29  tff(c_193, plain, (![A_71, C_73]: (k7_partfun1(A_71, '#skF_3', C_73)=k1_funct_1('#skF_3', C_73) | ~r2_hidden(C_73, '#skF_1') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_71) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_191])).
% 2.33/1.29  tff(c_200, plain, (![A_74, C_75]: (k7_partfun1(A_74, '#skF_3', C_75)=k1_funct_1('#skF_3', C_75) | ~r2_hidden(C_75, '#skF_1') | ~v5_relat_1('#skF_3', A_74))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_48, c_193])).
% 2.33/1.29  tff(c_203, plain, (![A_74, B_2]: (k7_partfun1(A_74, '#skF_3', B_2)=k1_funct_1('#skF_3', B_2) | ~v5_relat_1('#skF_3', A_74) | ~m1_subset_1(B_2, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_200])).
% 2.33/1.29  tff(c_207, plain, (![A_76, B_77]: (k7_partfun1(A_76, '#skF_3', B_77)=k1_funct_1('#skF_3', B_77) | ~v5_relat_1('#skF_3', A_76) | ~m1_subset_1(B_77, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_52, c_203])).
% 2.33/1.29  tff(c_211, plain, (![B_78]: (k7_partfun1('#skF_2', '#skF_3', B_78)=k1_funct_1('#skF_3', B_78) | ~m1_subset_1(B_78, '#skF_1'))), inference(resolution, [status(thm)], [c_116, c_207])).
% 2.33/1.29  tff(c_220, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_211])).
% 2.33/1.29  tff(c_40, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k7_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.33/1.29  tff(c_221, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_40])).
% 2.33/1.29  tff(c_233, plain, (![A_82, B_83, C_84, D_85]: (k3_funct_2(A_82, B_83, C_84, D_85)=k1_funct_1(C_84, D_85) | ~m1_subset_1(D_85, A_82) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(C_84, A_82, B_83) | ~v1_funct_1(C_84) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.33/1.29  tff(c_239, plain, (![B_83, C_84]: (k3_funct_2('#skF_1', B_83, C_84, '#skF_4')=k1_funct_1(C_84, '#skF_4') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_83))) | ~v1_funct_2(C_84, '#skF_1', B_83) | ~v1_funct_1(C_84) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_233])).
% 2.33/1.29  tff(c_247, plain, (![B_86, C_87]: (k3_funct_2('#skF_1', B_86, C_87, '#skF_4')=k1_funct_1(C_87, '#skF_4') | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_86))) | ~v1_funct_2(C_87, '#skF_1', B_86) | ~v1_funct_1(C_87))), inference(negUnitSimplification, [status(thm)], [c_52, c_239])).
% 2.33/1.29  tff(c_254, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_247])).
% 2.33/1.29  tff(c_258, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_254])).
% 2.33/1.29  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_258])).
% 2.33/1.29  tff(c_261, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_169])).
% 2.33/1.29  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.29  tff(c_269, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_4])).
% 2.33/1.29  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_269])).
% 2.33/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  Inference rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Ref     : 0
% 2.33/1.29  #Sup     : 44
% 2.33/1.29  #Fact    : 0
% 2.33/1.29  #Define  : 0
% 2.33/1.29  #Split   : 3
% 2.33/1.29  #Chain   : 0
% 2.33/1.29  #Close   : 0
% 2.33/1.29  
% 2.33/1.29  Ordering : KBO
% 2.33/1.29  
% 2.33/1.29  Simplification rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Subsume      : 14
% 2.33/1.29  #Demod        : 34
% 2.33/1.29  #Tautology    : 16
% 2.33/1.29  #SimpNegUnit  : 6
% 2.33/1.29  #BackRed      : 9
% 2.33/1.29  
% 2.33/1.29  #Partial instantiations: 0
% 2.33/1.29  #Strategies tried      : 1
% 2.33/1.29  
% 2.33/1.29  Timing (in seconds)
% 2.33/1.29  ----------------------
% 2.33/1.29  Preprocessing        : 0.33
% 2.33/1.29  Parsing              : 0.17
% 2.33/1.29  CNF conversion       : 0.02
% 2.33/1.29  Main loop            : 0.21
% 2.33/1.29  Inferencing          : 0.07
% 2.33/1.29  Reduction            : 0.06
% 2.33/1.29  Demodulation         : 0.04
% 2.33/1.29  BG Simplification    : 0.02
% 2.33/1.29  Subsumption          : 0.04
% 2.33/1.29  Abstraction          : 0.01
% 2.33/1.29  MUC search           : 0.00
% 2.33/1.29  Cooper               : 0.00
% 2.33/1.30  Total                : 0.57
% 2.33/1.30  Index Insertion      : 0.00
% 2.33/1.30  Index Deletion       : 0.00
% 2.33/1.30  Index Matching       : 0.00
% 2.33/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
