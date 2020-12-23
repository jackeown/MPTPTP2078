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
% DateTime   : Thu Dec  3 10:17:36 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 127 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 311 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_122,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_87,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_107,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_157,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_157])).

tff(c_167,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_115,c_160])).

tff(c_182,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_192,plain,(
    ! [A_85,B_86,C_87] :
      ( k7_partfun1(A_85,B_86,C_87) = k1_funct_1(B_86,C_87)
      | ~ r2_hidden(C_87,k1_relat_1(B_86))
      | ~ v1_funct_1(B_86)
      | ~ v5_relat_1(B_86,A_85)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_194,plain,(
    ! [A_85,C_87] :
      ( k7_partfun1(A_85,'#skF_4',C_87) = k1_funct_1('#skF_4',C_87)
      | ~ r2_hidden(C_87,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_85)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_192])).

tff(c_201,plain,(
    ! [A_88,C_89] :
      ( k7_partfun1(A_88,'#skF_4',C_89) = k1_funct_1('#skF_4',C_89)
      | ~ r2_hidden(C_89,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_44,c_194])).

tff(c_204,plain,(
    ! [A_88,A_4] :
      ( k7_partfun1(A_88,'#skF_4',A_4) = k1_funct_1('#skF_4',A_4)
      | ~ v5_relat_1('#skF_4',A_88)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_4,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_201])).

tff(c_208,plain,(
    ! [A_90,A_91] :
      ( k7_partfun1(A_90,'#skF_4',A_91) = k1_funct_1('#skF_4',A_91)
      | ~ v5_relat_1('#skF_4',A_90)
      | ~ m1_subset_1(A_91,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_204])).

tff(c_212,plain,(
    ! [A_92] :
      ( k7_partfun1('#skF_3','#skF_4',A_92) = k1_funct_1('#skF_4',A_92)
      | ~ m1_subset_1(A_92,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_95,c_208])).

tff(c_221,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_212])).

tff(c_36,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_222,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_36])).

tff(c_227,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k3_funct_2(A_93,B_94,C_95,D_96) = k1_funct_1(C_95,D_96)
      | ~ m1_subset_1(D_96,A_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_2(C_95,A_93,B_94)
      | ~ v1_funct_1(C_95)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_233,plain,(
    ! [B_94,C_95] :
      ( k3_funct_2('#skF_2',B_94,C_95,'#skF_5') = k1_funct_1(C_95,'#skF_5')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_94)))
      | ~ v1_funct_2(C_95,'#skF_2',B_94)
      | ~ v1_funct_1(C_95)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_227])).

tff(c_259,plain,(
    ! [B_101,C_102] :
      ( k3_funct_2('#skF_2',B_101,C_102,'#skF_5') = k1_funct_1(C_102,'#skF_5')
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_101)))
      | ~ v1_funct_2(C_102,'#skF_2',B_101)
      | ~ v1_funct_1(C_102) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_233])).

tff(c_262,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_259])).

tff(c_269,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_262])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_269])).

tff(c_272,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [B_57,A_58] :
      ( ~ r1_tarski(B_57,A_58)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_66,c_12])).

tff(c_86,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_98,plain,(
    ! [A_62] : ~ m1_subset_1(A_62,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_103,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_104,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_282,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_104])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:33:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.33  
% 2.28/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.28/1.33  
% 2.28/1.33  %Foreground sorts:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Background operators:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Foreground operators:
% 2.28/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.33  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.28/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.33  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.28/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.33  
% 2.28/1.35  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.28/1.35  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.28/1.35  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.28/1.35  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.28/1.35  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.28/1.35  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.28/1.35  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.28/1.35  tff(f_89, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.28/1.35  tff(f_102, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.28/1.35  tff(f_30, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.28/1.35  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.28/1.35  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.28/1.35  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.28/1.35  tff(c_38, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.28/1.35  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.28/1.35  tff(c_87, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.35  tff(c_95, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_87])).
% 2.28/1.35  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.28/1.35  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.28/1.35  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.35  tff(c_53, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.35  tff(c_56, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_53])).
% 2.28/1.35  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 2.28/1.35  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.28/1.35  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.28/1.35  tff(c_107, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.28/1.35  tff(c_115, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.28/1.35  tff(c_157, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.35  tff(c_160, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_157])).
% 2.28/1.35  tff(c_167, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_115, c_160])).
% 2.28/1.35  tff(c_182, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_167])).
% 2.28/1.35  tff(c_192, plain, (![A_85, B_86, C_87]: (k7_partfun1(A_85, B_86, C_87)=k1_funct_1(B_86, C_87) | ~r2_hidden(C_87, k1_relat_1(B_86)) | ~v1_funct_1(B_86) | ~v5_relat_1(B_86, A_85) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.28/1.35  tff(c_194, plain, (![A_85, C_87]: (k7_partfun1(A_85, '#skF_4', C_87)=k1_funct_1('#skF_4', C_87) | ~r2_hidden(C_87, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_85) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_192])).
% 2.28/1.35  tff(c_201, plain, (![A_88, C_89]: (k7_partfun1(A_88, '#skF_4', C_89)=k1_funct_1('#skF_4', C_89) | ~r2_hidden(C_89, '#skF_2') | ~v5_relat_1('#skF_4', A_88))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_44, c_194])).
% 2.28/1.35  tff(c_204, plain, (![A_88, A_4]: (k7_partfun1(A_88, '#skF_4', A_4)=k1_funct_1('#skF_4', A_4) | ~v5_relat_1('#skF_4', A_88) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_4, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_201])).
% 2.28/1.35  tff(c_208, plain, (![A_90, A_91]: (k7_partfun1(A_90, '#skF_4', A_91)=k1_funct_1('#skF_4', A_91) | ~v5_relat_1('#skF_4', A_90) | ~m1_subset_1(A_91, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_204])).
% 2.28/1.35  tff(c_212, plain, (![A_92]: (k7_partfun1('#skF_3', '#skF_4', A_92)=k1_funct_1('#skF_4', A_92) | ~m1_subset_1(A_92, '#skF_2'))), inference(resolution, [status(thm)], [c_95, c_208])).
% 2.28/1.35  tff(c_221, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_212])).
% 2.28/1.35  tff(c_36, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.28/1.35  tff(c_222, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_36])).
% 2.28/1.35  tff(c_227, plain, (![A_93, B_94, C_95, D_96]: (k3_funct_2(A_93, B_94, C_95, D_96)=k1_funct_1(C_95, D_96) | ~m1_subset_1(D_96, A_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_2(C_95, A_93, B_94) | ~v1_funct_1(C_95) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.28/1.35  tff(c_233, plain, (![B_94, C_95]: (k3_funct_2('#skF_2', B_94, C_95, '#skF_5')=k1_funct_1(C_95, '#skF_5') | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_94))) | ~v1_funct_2(C_95, '#skF_2', B_94) | ~v1_funct_1(C_95) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_227])).
% 2.28/1.35  tff(c_259, plain, (![B_101, C_102]: (k3_funct_2('#skF_2', B_101, C_102, '#skF_5')=k1_funct_1(C_102, '#skF_5') | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_101))) | ~v1_funct_2(C_102, '#skF_2', B_101) | ~v1_funct_1(C_102))), inference(negUnitSimplification, [status(thm)], [c_48, c_233])).
% 2.28/1.35  tff(c_262, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_259])).
% 2.28/1.35  tff(c_269, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_262])).
% 2.28/1.35  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_269])).
% 2.28/1.35  tff(c_272, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_167])).
% 2.28/1.35  tff(c_4, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.28/1.35  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.35  tff(c_66, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | v1_xboole_0(B_51) | ~m1_subset_1(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.28/1.35  tff(c_12, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.35  tff(c_82, plain, (![B_57, A_58]: (~r1_tarski(B_57, A_58) | v1_xboole_0(B_57) | ~m1_subset_1(A_58, B_57))), inference(resolution, [status(thm)], [c_66, c_12])).
% 2.28/1.35  tff(c_86, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_82])).
% 2.28/1.35  tff(c_98, plain, (![A_62]: (~m1_subset_1(A_62, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_86])).
% 2.28/1.35  tff(c_103, plain, $false, inference(resolution, [status(thm)], [c_4, c_98])).
% 2.28/1.35  tff(c_104, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_86])).
% 2.28/1.35  tff(c_282, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_104])).
% 2.28/1.35  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_282])).
% 2.28/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  Inference rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Ref     : 0
% 2.28/1.35  #Sup     : 45
% 2.28/1.35  #Fact    : 0
% 2.28/1.35  #Define  : 0
% 2.28/1.35  #Split   : 2
% 2.28/1.35  #Chain   : 0
% 2.28/1.35  #Close   : 0
% 2.28/1.35  
% 2.28/1.35  Ordering : KBO
% 2.28/1.35  
% 2.28/1.35  Simplification rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Subsume      : 0
% 2.28/1.35  #Demod        : 44
% 2.28/1.35  #Tautology    : 17
% 2.28/1.35  #SimpNegUnit  : 4
% 2.28/1.35  #BackRed      : 12
% 2.28/1.35  
% 2.28/1.35  #Partial instantiations: 0
% 2.28/1.35  #Strategies tried      : 1
% 2.28/1.35  
% 2.28/1.35  Timing (in seconds)
% 2.28/1.35  ----------------------
% 2.28/1.35  Preprocessing        : 0.33
% 2.28/1.35  Parsing              : 0.18
% 2.28/1.35  CNF conversion       : 0.02
% 2.28/1.36  Main loop            : 0.23
% 2.28/1.36  Inferencing          : 0.09
% 2.28/1.36  Reduction            : 0.07
% 2.28/1.36  Demodulation         : 0.05
% 2.28/1.36  BG Simplification    : 0.02
% 2.28/1.36  Subsumption          : 0.03
% 2.28/1.36  Abstraction          : 0.01
% 2.28/1.36  MUC search           : 0.00
% 2.28/1.36  Cooper               : 0.00
% 2.28/1.36  Total                : 0.60
% 2.28/1.36  Index Insertion      : 0.00
% 2.28/1.36  Index Deletion       : 0.00
% 2.28/1.36  Index Matching       : 0.00
% 2.28/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
