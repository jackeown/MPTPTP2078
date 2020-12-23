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
% DateTime   : Thu Dec  3 10:17:35 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 103 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 268 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_108,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_78,plain,(
    ! [B_58,A_59,C_60] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_59,B_58,C_60) = A_59
      | ~ v1_funct_2(C_60,A_59,B_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_64,c_81])).

tff(c_85,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_91,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_partfun1(A_61,B_62,C_63) = k1_funct_1(B_62,C_63)
      | ~ r2_hidden(C_63,k1_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | ~ v5_relat_1(B_62,A_61)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,(
    ! [A_61,C_63] :
      ( k7_partfun1(A_61,'#skF_3',C_63) = k1_funct_1('#skF_3',C_63)
      | ~ r2_hidden(C_63,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_61)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_91])).

tff(c_104,plain,(
    ! [A_64,C_65] :
      ( k7_partfun1(A_64,'#skF_3',C_65) = k1_funct_1('#skF_3',C_65)
      | ~ r2_hidden(C_65,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_93])).

tff(c_107,plain,(
    ! [A_64,A_1] :
      ( k7_partfun1(A_64,'#skF_3',A_1) = k1_funct_1('#skF_3',A_1)
      | ~ v5_relat_1('#skF_3',A_64)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_111,plain,(
    ! [A_66,A_67] :
      ( k7_partfun1(A_66,'#skF_3',A_67) = k1_funct_1('#skF_3',A_67)
      | ~ v5_relat_1('#skF_3',A_66)
      | ~ m1_subset_1(A_67,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_107])).

tff(c_115,plain,(
    ! [A_68] :
      ( k7_partfun1('#skF_2','#skF_3',A_68) = k1_funct_1('#skF_3',A_68)
      | ~ m1_subset_1(A_68,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_119,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_30,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_120,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_30])).

tff(c_132,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k3_funct_2(A_72,B_73,C_74,D_75) = k1_funct_1(C_74,D_75)
      | ~ m1_subset_1(D_75,A_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(C_74,A_72,B_73)
      | ~ v1_funct_1(C_74)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_136,plain,(
    ! [B_73,C_74] :
      ( k3_funct_2('#skF_1',B_73,C_74,'#skF_4') = k1_funct_1(C_74,'#skF_4')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_73)))
      | ~ v1_funct_2(C_74,'#skF_1',B_73)
      | ~ v1_funct_1(C_74)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_141,plain,(
    ! [B_76,C_77] :
      ( k3_funct_2('#skF_1',B_76,C_77,'#skF_4') = k1_funct_1(C_77,'#skF_4')
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_76)))
      | ~ v1_funct_2(C_77,'#skF_1',B_76)
      | ~ v1_funct_1(C_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_136])).

tff(c_144,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_141])).

tff(c_147,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_144])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_147])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_163,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_2])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.25  
% 2.22/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.25  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.25  
% 2.22/1.25  %Foreground sorts:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Background operators:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Foreground operators:
% 2.22/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.25  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.22/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.22/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.22/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.25  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.22/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.25  
% 2.22/1.27  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.22/1.27  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.27  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.22/1.27  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.27  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.22/1.27  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.22/1.27  tff(f_75, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.22/1.27  tff(f_88, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.22/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.22/1.27  tff(c_40, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.22/1.27  tff(c_32, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.22/1.27  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.22/1.27  tff(c_54, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.27  tff(c_58, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.22/1.27  tff(c_42, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.22/1.27  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.27  tff(c_44, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.27  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.22/1.27  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.22/1.27  tff(c_36, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.22/1.27  tff(c_60, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.27  tff(c_64, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_60])).
% 2.22/1.27  tff(c_78, plain, (![B_58, A_59, C_60]: (k1_xboole_0=B_58 | k1_relset_1(A_59, B_58, C_60)=A_59 | ~v1_funct_2(C_60, A_59, B_58) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.27  tff(c_81, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_78])).
% 2.22/1.27  tff(c_84, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_64, c_81])).
% 2.22/1.27  tff(c_85, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_84])).
% 2.22/1.27  tff(c_91, plain, (![A_61, B_62, C_63]: (k7_partfun1(A_61, B_62, C_63)=k1_funct_1(B_62, C_63) | ~r2_hidden(C_63, k1_relat_1(B_62)) | ~v1_funct_1(B_62) | ~v5_relat_1(B_62, A_61) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.27  tff(c_93, plain, (![A_61, C_63]: (k7_partfun1(A_61, '#skF_3', C_63)=k1_funct_1('#skF_3', C_63) | ~r2_hidden(C_63, '#skF_1') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_61) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_91])).
% 2.22/1.27  tff(c_104, plain, (![A_64, C_65]: (k7_partfun1(A_64, '#skF_3', C_65)=k1_funct_1('#skF_3', C_65) | ~r2_hidden(C_65, '#skF_1') | ~v5_relat_1('#skF_3', A_64))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_93])).
% 2.22/1.27  tff(c_107, plain, (![A_64, A_1]: (k7_partfun1(A_64, '#skF_3', A_1)=k1_funct_1('#skF_3', A_1) | ~v5_relat_1('#skF_3', A_64) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_104])).
% 2.22/1.27  tff(c_111, plain, (![A_66, A_67]: (k7_partfun1(A_66, '#skF_3', A_67)=k1_funct_1('#skF_3', A_67) | ~v5_relat_1('#skF_3', A_66) | ~m1_subset_1(A_67, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_107])).
% 2.22/1.27  tff(c_115, plain, (![A_68]: (k7_partfun1('#skF_2', '#skF_3', A_68)=k1_funct_1('#skF_3', A_68) | ~m1_subset_1(A_68, '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_111])).
% 2.22/1.27  tff(c_119, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_115])).
% 2.22/1.27  tff(c_30, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k7_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.22/1.27  tff(c_120, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_30])).
% 2.22/1.27  tff(c_132, plain, (![A_72, B_73, C_74, D_75]: (k3_funct_2(A_72, B_73, C_74, D_75)=k1_funct_1(C_74, D_75) | ~m1_subset_1(D_75, A_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(C_74, A_72, B_73) | ~v1_funct_1(C_74) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.22/1.27  tff(c_136, plain, (![B_73, C_74]: (k3_funct_2('#skF_1', B_73, C_74, '#skF_4')=k1_funct_1(C_74, '#skF_4') | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_73))) | ~v1_funct_2(C_74, '#skF_1', B_73) | ~v1_funct_1(C_74) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_132])).
% 2.22/1.27  tff(c_141, plain, (![B_76, C_77]: (k3_funct_2('#skF_1', B_76, C_77, '#skF_4')=k1_funct_1(C_77, '#skF_4') | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_76))) | ~v1_funct_2(C_77, '#skF_1', B_76) | ~v1_funct_1(C_77))), inference(negUnitSimplification, [status(thm)], [c_42, c_136])).
% 2.22/1.27  tff(c_144, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_141])).
% 2.22/1.27  tff(c_147, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_144])).
% 2.22/1.27  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_147])).
% 2.22/1.27  tff(c_150, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_84])).
% 2.22/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.22/1.27  tff(c_163, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_2])).
% 2.22/1.27  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_163])).
% 2.22/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  Inference rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Ref     : 0
% 2.22/1.27  #Sup     : 24
% 2.22/1.27  #Fact    : 0
% 2.22/1.27  #Define  : 0
% 2.22/1.27  #Split   : 1
% 2.22/1.27  #Chain   : 0
% 2.22/1.27  #Close   : 0
% 2.22/1.27  
% 2.22/1.27  Ordering : KBO
% 2.22/1.27  
% 2.22/1.27  Simplification rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Subsume      : 1
% 2.22/1.27  #Demod        : 34
% 2.22/1.27  #Tautology    : 9
% 2.22/1.27  #SimpNegUnit  : 5
% 2.22/1.27  #BackRed      : 9
% 2.22/1.27  
% 2.22/1.27  #Partial instantiations: 0
% 2.22/1.27  #Strategies tried      : 1
% 2.22/1.27  
% 2.22/1.27  Timing (in seconds)
% 2.22/1.27  ----------------------
% 2.22/1.27  Preprocessing        : 0.33
% 2.22/1.27  Parsing              : 0.17
% 2.22/1.27  CNF conversion       : 0.02
% 2.22/1.27  Main loop            : 0.18
% 2.22/1.27  Inferencing          : 0.07
% 2.22/1.27  Reduction            : 0.06
% 2.22/1.27  Demodulation         : 0.04
% 2.22/1.27  BG Simplification    : 0.01
% 2.22/1.27  Subsumption          : 0.03
% 2.22/1.27  Abstraction          : 0.01
% 2.22/1.27  MUC search           : 0.00
% 2.22/1.27  Cooper               : 0.00
% 2.22/1.27  Total                : 0.54
% 2.22/1.27  Index Insertion      : 0.00
% 2.22/1.27  Index Deletion       : 0.00
% 2.22/1.27  Index Matching       : 0.00
% 2.22/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
