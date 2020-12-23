%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:20 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 514 expanded)
%              Number of leaves         :   35 ( 188 expanded)
%              Depth                    :   15
%              Number of atoms          :  160 (1394 expanded)
%              Number of equality atoms :   43 ( 267 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_127,negated_conjecture,(
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

tff(f_92,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_76,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_158,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_funct_2(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(D_69,A_67,B_68)
      | ~ v1_funct_1(D_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_160,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_158])).

tff(c_163,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_160])).

tff(c_61,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_61])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_67,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_79,plain,(
    ! [B_48,A_49] :
      ( k1_relat_1(B_48) = A_49
      | ~ v1_partfun1(B_48,A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_82,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_79])).

tff(c_85,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_82])).

tff(c_86,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_101,plain,(
    ! [B_59,C_60,A_61] :
      ( k1_xboole_0 = B_59
      | v1_partfun1(C_60,A_61)
      | ~ v1_funct_2(C_60,A_61,B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_59)))
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_104,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_107,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_104])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_107])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_111,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_111])).

tff(c_114,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_26,plain,(
    ! [A_20] : k6_relat_1(A_20) = k6_partfun1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_66),B_66),k1_relat_1(B_66))
      | k6_partfun1(k1_relat_1(B_66)) = B_66
      | ~ v1_funct_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_134,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_128])).

tff(c_140,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_114,c_114,c_134])).

tff(c_143,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_36,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_144,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_36])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_144])).

tff(c_167,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_6,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [B_77] :
      ( k1_funct_1(B_77,'#skF_1'(k1_relat_1(B_77),B_77)) != '#skF_1'(k1_relat_1(B_77),B_77)
      | k6_partfun1(k1_relat_1(B_77)) = B_77
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_211,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_208])).

tff(c_213,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_114,c_114,c_211])).

tff(c_214,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_213])).

tff(c_137,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_3'),'#skF_2')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_128])).

tff(c_142,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_114,c_114,c_137])).

tff(c_168,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_142])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_172,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_38,plain,(
    ! [C_32] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_32) = C_32
      | ~ m1_subset_1(C_32,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_177,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_38])).

tff(c_215,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k3_funct_2(A_78,B_79,C_80,D_81) = k1_funct_1(C_80,D_81)
      | ~ m1_subset_1(D_81,A_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(C_80,A_78,B_79)
      | ~ v1_funct_1(C_80)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_219,plain,(
    ! [B_79,C_80] :
      ( k3_funct_2('#skF_2',B_79,C_80,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_80,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_79)))
      | ~ v1_funct_2(C_80,'#skF_2',B_79)
      | ~ v1_funct_1(C_80)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_172,c_215])).

tff(c_227,plain,(
    ! [B_82,C_83] :
      ( k3_funct_2('#skF_2',B_82,C_83,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_83,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_82)))
      | ~ v1_funct_2(C_83,'#skF_2',B_82)
      | ~ v1_funct_1(C_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_219])).

tff(c_230,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_227])).

tff(c_233,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_177,c_230])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.32  
% 2.20/1.32  %Foreground sorts:
% 2.20/1.32  
% 2.20/1.32  
% 2.20/1.32  %Background operators:
% 2.20/1.32  
% 2.20/1.32  
% 2.20/1.32  %Foreground operators:
% 2.20/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.20/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.20/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.20/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.20/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.32  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.20/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.32  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.20/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.32  
% 2.47/1.34  tff(f_127, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.47/1.34  tff(f_92, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.47/1.34  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.47/1.34  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.47/1.34  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.47/1.34  tff(f_109, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.47/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.47/1.34  tff(f_76, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.47/1.34  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.47/1.34  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.47/1.34  tff(f_74, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.47/1.34  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.47/1.34  tff(c_42, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.47/1.34  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.47/1.34  tff(c_158, plain, (![A_67, B_68, D_69]: (r2_funct_2(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(D_69, A_67, B_68) | ~v1_funct_1(D_69))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.34  tff(c_160, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_158])).
% 2.47/1.34  tff(c_163, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_160])).
% 2.47/1.34  tff(c_61, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.47/1.34  tff(c_65, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_61])).
% 2.47/1.34  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.47/1.34  tff(c_67, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.34  tff(c_71, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.47/1.34  tff(c_79, plain, (![B_48, A_49]: (k1_relat_1(B_48)=A_49 | ~v1_partfun1(B_48, A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/1.34  tff(c_82, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_79])).
% 2.47/1.34  tff(c_85, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_82])).
% 2.47/1.34  tff(c_86, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_85])).
% 2.47/1.34  tff(c_101, plain, (![B_59, C_60, A_61]: (k1_xboole_0=B_59 | v1_partfun1(C_60, A_61) | ~v1_funct_2(C_60, A_61, B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_59))) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.47/1.34  tff(c_104, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_101])).
% 2.47/1.34  tff(c_107, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_104])).
% 2.47/1.34  tff(c_108, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_107])).
% 2.47/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.47/1.34  tff(c_111, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2])).
% 2.47/1.34  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_111])).
% 2.47/1.34  tff(c_114, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_85])).
% 2.47/1.34  tff(c_26, plain, (![A_20]: (k6_relat_1(A_20)=k6_partfun1(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.34  tff(c_8, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.34  tff(c_128, plain, (![B_66]: (r2_hidden('#skF_1'(k1_relat_1(B_66), B_66), k1_relat_1(B_66)) | k6_partfun1(k1_relat_1(B_66))=B_66 | ~v1_funct_1(B_66) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 2.47/1.34  tff(c_134, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_114, c_128])).
% 2.47/1.34  tff(c_140, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_114, c_114, c_134])).
% 2.47/1.34  tff(c_143, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_140])).
% 2.47/1.34  tff(c_36, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.47/1.34  tff(c_144, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_36])).
% 2.47/1.34  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_144])).
% 2.47/1.34  tff(c_167, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_140])).
% 2.47/1.34  tff(c_6, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.34  tff(c_208, plain, (![B_77]: (k1_funct_1(B_77, '#skF_1'(k1_relat_1(B_77), B_77))!='#skF_1'(k1_relat_1(B_77), B_77) | k6_partfun1(k1_relat_1(B_77))=B_77 | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 2.47/1.34  tff(c_211, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_114, c_208])).
% 2.47/1.34  tff(c_213, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_114, c_114, c_211])).
% 2.47/1.34  tff(c_214, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_167, c_213])).
% 2.47/1.34  tff(c_137, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_3'), '#skF_2') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_114, c_128])).
% 2.47/1.34  tff(c_142, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_114, c_114, c_137])).
% 2.47/1.34  tff(c_168, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_167, c_142])).
% 2.47/1.34  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.47/1.34  tff(c_172, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_168, c_4])).
% 2.47/1.34  tff(c_38, plain, (![C_32]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_32)=C_32 | ~m1_subset_1(C_32, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.47/1.34  tff(c_177, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_172, c_38])).
% 2.47/1.34  tff(c_215, plain, (![A_78, B_79, C_80, D_81]: (k3_funct_2(A_78, B_79, C_80, D_81)=k1_funct_1(C_80, D_81) | ~m1_subset_1(D_81, A_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(C_80, A_78, B_79) | ~v1_funct_1(C_80) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.34  tff(c_219, plain, (![B_79, C_80]: (k3_funct_2('#skF_2', B_79, C_80, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_80, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_79))) | ~v1_funct_2(C_80, '#skF_2', B_79) | ~v1_funct_1(C_80) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_172, c_215])).
% 2.47/1.34  tff(c_227, plain, (![B_82, C_83]: (k3_funct_2('#skF_2', B_82, C_83, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_83, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_82))) | ~v1_funct_2(C_83, '#skF_2', B_82) | ~v1_funct_1(C_83))), inference(negUnitSimplification, [status(thm)], [c_46, c_219])).
% 2.47/1.34  tff(c_230, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_227])).
% 2.47/1.34  tff(c_233, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_177, c_230])).
% 2.47/1.34  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_233])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 33
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 2
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 0
% 2.47/1.34  #Demod        : 66
% 2.47/1.34  #Tautology    : 14
% 2.47/1.34  #SimpNegUnit  : 8
% 2.47/1.34  #BackRed      : 4
% 2.47/1.34  
% 2.47/1.34  #Partial instantiations: 0
% 2.47/1.34  #Strategies tried      : 1
% 2.47/1.34  
% 2.47/1.34  Timing (in seconds)
% 2.47/1.34  ----------------------
% 2.47/1.34  Preprocessing        : 0.34
% 2.47/1.34  Parsing              : 0.18
% 2.47/1.34  CNF conversion       : 0.02
% 2.47/1.34  Main loop            : 0.19
% 2.47/1.34  Inferencing          : 0.07
% 2.47/1.34  Reduction            : 0.06
% 2.47/1.34  Demodulation         : 0.05
% 2.47/1.34  BG Simplification    : 0.02
% 2.47/1.34  Subsumption          : 0.03
% 2.47/1.34  Abstraction          : 0.01
% 2.47/1.34  MUC search           : 0.00
% 2.47/1.34  Cooper               : 0.00
% 2.47/1.34  Total                : 0.57
% 2.47/1.34  Index Insertion      : 0.00
% 2.47/1.34  Index Deletion       : 0.00
% 2.47/1.34  Index Matching       : 0.00
% 2.47/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
