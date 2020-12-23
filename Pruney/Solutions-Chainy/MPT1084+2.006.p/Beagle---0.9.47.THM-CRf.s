%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:20 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 389 expanded)
%              Number of leaves         :   33 ( 146 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 (1054 expanded)
%              Number of equality atoms :   35 ( 195 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_120,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_funct_2(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_funct_2(D_65,A_63,B_64)
      | ~ v1_funct_1(D_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_122,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_125,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_122])).

tff(c_59,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_70,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_77,plain,(
    ! [B_49,A_50] :
      ( k1_relat_1(B_49) = A_50
      | ~ v1_partfun1(B_49,A_50)
      | ~ v4_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_80,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_77])).

tff(c_83,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_80])).

tff(c_84,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_98,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_partfun1(C_58,A_59)
      | ~ v1_funct_2(C_58,A_59,B_60)
      | ~ v1_funct_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | v1_xboole_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_104,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_101])).

tff(c_106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_84,c_104])).

tff(c_107,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_28,plain,(
    ! [A_24] : k6_relat_1(A_24) = k6_partfun1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_126,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_66),B_66),k1_relat_1(B_66))
      | k6_partfun1(k1_relat_1(B_66)) = B_66
      | ~ v1_funct_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_132,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_126])).

tff(c_138,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_107,c_107,c_132])).

tff(c_141,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_34,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_142,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_34])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_142])).

tff(c_147,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_4,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_183,plain,(
    ! [B_71] :
      ( k1_funct_1(B_71,'#skF_1'(k1_relat_1(B_71),B_71)) != '#skF_1'(k1_relat_1(B_71),B_71)
      | k6_partfun1(k1_relat_1(B_71)) = B_71
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4])).

tff(c_186,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_183])).

tff(c_188,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_107,c_107,c_186])).

tff(c_189,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_188])).

tff(c_146,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_36,plain,(
    ! [C_33] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_33) = C_33
      | ~ m1_subset_1(C_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_163,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_36])).

tff(c_190,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k3_funct_2(A_72,B_73,C_74,D_75) = k1_funct_1(C_74,D_75)
      | ~ m1_subset_1(D_75,A_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(C_74,A_72,B_73)
      | ~ v1_funct_1(C_74)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_194,plain,(
    ! [B_73,C_74] :
      ( k3_funct_2('#skF_2',B_73,C_74,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_74,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_73)))
      | ~ v1_funct_2(C_74,'#skF_2',B_73)
      | ~ v1_funct_1(C_74)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_159,c_190])).

tff(c_202,plain,(
    ! [B_76,C_77] :
      ( k3_funct_2('#skF_2',B_76,C_77,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_77,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_76)))
      | ~ v1_funct_2(C_77,'#skF_2',B_76)
      | ~ v1_funct_1(C_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_194])).

tff(c_205,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_202])).

tff(c_208,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_163,c_205])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.12/1.27  
% 2.12/1.27  %Foreground sorts:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Background operators:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Foreground operators:
% 2.12/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.12/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.12/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.12/1.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.12/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.27  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.12/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.27  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.12/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.27  
% 2.35/1.29  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.35/1.29  tff(f_105, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.35/1.29  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.35/1.29  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.35/1.29  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.35/1.29  tff(f_66, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.35/1.29  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.35/1.29  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.35/1.29  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.35/1.29  tff(f_87, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.35/1.29  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.35/1.29  tff(c_40, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.35/1.29  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.35/1.29  tff(c_120, plain, (![A_63, B_64, D_65]: (r2_funct_2(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~v1_funct_2(D_65, A_63, B_64) | ~v1_funct_1(D_65))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.35/1.29  tff(c_122, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_120])).
% 2.35/1.29  tff(c_125, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_122])).
% 2.35/1.29  tff(c_59, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.35/1.29  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_59])).
% 2.35/1.29  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.35/1.29  tff(c_70, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.35/1.29  tff(c_74, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_70])).
% 2.35/1.29  tff(c_77, plain, (![B_49, A_50]: (k1_relat_1(B_49)=A_50 | ~v1_partfun1(B_49, A_50) | ~v4_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.29  tff(c_80, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_77])).
% 2.35/1.29  tff(c_83, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_80])).
% 2.35/1.29  tff(c_84, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_83])).
% 2.35/1.29  tff(c_98, plain, (![C_58, A_59, B_60]: (v1_partfun1(C_58, A_59) | ~v1_funct_2(C_58, A_59, B_60) | ~v1_funct_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | v1_xboole_0(B_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.35/1.29  tff(c_101, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_98])).
% 2.35/1.29  tff(c_104, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_101])).
% 2.35/1.29  tff(c_106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_84, c_104])).
% 2.35/1.29  tff(c_107, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 2.35/1.29  tff(c_28, plain, (![A_24]: (k6_relat_1(A_24)=k6_partfun1(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.29  tff(c_6, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.29  tff(c_126, plain, (![B_66]: (r2_hidden('#skF_1'(k1_relat_1(B_66), B_66), k1_relat_1(B_66)) | k6_partfun1(k1_relat_1(B_66))=B_66 | ~v1_funct_1(B_66) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6])).
% 2.35/1.29  tff(c_132, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_126])).
% 2.35/1.29  tff(c_138, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_107, c_107, c_132])).
% 2.35/1.29  tff(c_141, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_138])).
% 2.35/1.29  tff(c_34, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.35/1.29  tff(c_142, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_34])).
% 2.35/1.29  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_142])).
% 2.35/1.29  tff(c_147, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_138])).
% 2.35/1.29  tff(c_4, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.29  tff(c_183, plain, (![B_71]: (k1_funct_1(B_71, '#skF_1'(k1_relat_1(B_71), B_71))!='#skF_1'(k1_relat_1(B_71), B_71) | k6_partfun1(k1_relat_1(B_71))=B_71 | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4])).
% 2.35/1.29  tff(c_186, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_183])).
% 2.35/1.29  tff(c_188, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_107, c_107, c_186])).
% 2.35/1.29  tff(c_189, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_147, c_188])).
% 2.35/1.29  tff(c_146, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_138])).
% 2.35/1.29  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.29  tff(c_159, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_146, c_2])).
% 2.35/1.29  tff(c_36, plain, (![C_33]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_33)=C_33 | ~m1_subset_1(C_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.35/1.29  tff(c_163, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_159, c_36])).
% 2.35/1.29  tff(c_190, plain, (![A_72, B_73, C_74, D_75]: (k3_funct_2(A_72, B_73, C_74, D_75)=k1_funct_1(C_74, D_75) | ~m1_subset_1(D_75, A_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(C_74, A_72, B_73) | ~v1_funct_1(C_74) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.35/1.29  tff(c_194, plain, (![B_73, C_74]: (k3_funct_2('#skF_2', B_73, C_74, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_74, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_73))) | ~v1_funct_2(C_74, '#skF_2', B_73) | ~v1_funct_1(C_74) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_159, c_190])).
% 2.35/1.29  tff(c_202, plain, (![B_76, C_77]: (k3_funct_2('#skF_2', B_76, C_77, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_77, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_76))) | ~v1_funct_2(C_77, '#skF_2', B_76) | ~v1_funct_1(C_77))), inference(negUnitSimplification, [status(thm)], [c_44, c_194])).
% 2.35/1.29  tff(c_205, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_202])).
% 2.35/1.29  tff(c_208, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_163, c_205])).
% 2.35/1.29  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_208])).
% 2.35/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.29  
% 2.35/1.29  Inference rules
% 2.35/1.29  ----------------------
% 2.35/1.29  #Ref     : 0
% 2.35/1.29  #Sup     : 28
% 2.35/1.29  #Fact    : 0
% 2.35/1.29  #Define  : 0
% 2.35/1.29  #Split   : 2
% 2.35/1.29  #Chain   : 0
% 2.35/1.29  #Close   : 0
% 2.35/1.29  
% 2.35/1.29  Ordering : KBO
% 2.35/1.29  
% 2.35/1.29  Simplification rules
% 2.35/1.29  ----------------------
% 2.35/1.29  #Subsume      : 0
% 2.35/1.29  #Demod        : 50
% 2.35/1.29  #Tautology    : 12
% 2.35/1.29  #SimpNegUnit  : 8
% 2.35/1.29  #BackRed      : 1
% 2.35/1.29  
% 2.35/1.29  #Partial instantiations: 0
% 2.35/1.29  #Strategies tried      : 1
% 2.35/1.29  
% 2.35/1.29  Timing (in seconds)
% 2.35/1.29  ----------------------
% 2.35/1.30  Preprocessing        : 0.33
% 2.35/1.30  Parsing              : 0.17
% 2.35/1.30  CNF conversion       : 0.02
% 2.35/1.30  Main loop            : 0.19
% 2.35/1.30  Inferencing          : 0.07
% 2.35/1.30  Reduction            : 0.06
% 2.35/1.30  Demodulation         : 0.04
% 2.35/1.30  BG Simplification    : 0.02
% 2.35/1.30  Subsumption          : 0.02
% 2.35/1.30  Abstraction          : 0.01
% 2.35/1.30  MUC search           : 0.00
% 2.35/1.30  Cooper               : 0.00
% 2.35/1.30  Total                : 0.55
% 2.35/1.30  Index Insertion      : 0.00
% 2.35/1.30  Index Deletion       : 0.00
% 2.35/1.30  Index Matching       : 0.00
% 2.35/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
