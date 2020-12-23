%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:22 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 452 expanded)
%              Number of leaves         :   34 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 (1180 expanded)
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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_128,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_94,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_65,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_70,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_82,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(B_52) = A_53
      | ~ v1_partfun1(B_52,A_53)
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_85,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_82])).

tff(c_88,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_85])).

tff(c_89,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_42,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_103,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_partfun1(C_61,A_62)
      | ~ v1_funct_2(C_61,A_62,B_63)
      | ~ v1_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | v1_xboole_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_103])).

tff(c_109,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_106])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_89,c_109])).

tff(c_112,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_30,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,(
    ! [B_69] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_69),B_69),k1_relat_1(B_69))
      | k6_partfun1(k1_relat_1(B_69)) = B_69
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_139,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_133])).

tff(c_145,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44,c_112,c_112,c_139])).

tff(c_148,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_36,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_149,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_36])).

tff(c_163,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_funct_2(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(D_72,A_70,B_71)
      | ~ v1_funct_1(D_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_165,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_163])).

tff(c_168,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_165])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_168])).

tff(c_172,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_8,plain,(
    ! [B_9] :
      ( k1_funct_1(B_9,'#skF_1'(k1_relat_1(B_9),B_9)) != '#skF_1'(k1_relat_1(B_9),B_9)
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [B_77] :
      ( k1_funct_1(B_77,'#skF_1'(k1_relat_1(B_77),B_77)) != '#skF_1'(k1_relat_1(B_77),B_77)
      | k6_partfun1(k1_relat_1(B_77)) = B_77
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_209,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_206])).

tff(c_211,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44,c_112,c_112,c_209])).

tff(c_212,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_211])).

tff(c_171,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_176,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_171,c_2])).

tff(c_38,plain,(
    ! [C_35] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_35) = C_35
      | ~ m1_subset_1(C_35,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_180,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_38])).

tff(c_213,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k3_funct_2(A_78,B_79,C_80,D_81) = k1_funct_1(C_80,D_81)
      | ~ m1_subset_1(D_81,A_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(C_80,A_78,B_79)
      | ~ v1_funct_1(C_80)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_217,plain,(
    ! [B_79,C_80] :
      ( k3_funct_2('#skF_2',B_79,C_80,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_80,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_79)))
      | ~ v1_funct_2(C_80,'#skF_2',B_79)
      | ~ v1_funct_1(C_80)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_176,c_213])).

tff(c_225,plain,(
    ! [B_82,C_83] :
      ( k3_funct_2('#skF_2',B_82,C_83,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_83,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_82)))
      | ~ v1_funct_2(C_83,'#skF_2',B_82)
      | ~ v1_funct_1(C_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_217])).

tff(c_228,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_225])).

tff(c_231,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_180,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.24  
% 2.28/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.24  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.24  
% 2.28/1.24  %Foreground sorts:
% 2.28/1.24  
% 2.28/1.24  
% 2.28/1.24  %Background operators:
% 2.28/1.24  
% 2.28/1.24  
% 2.28/1.24  %Foreground operators:
% 2.28/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.28/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.28/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.28/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.24  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.28/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.24  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.28/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.24  
% 2.28/1.26  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.28/1.26  tff(f_128, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.28/1.26  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.28/1.26  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.28/1.26  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.28/1.26  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.28/1.26  tff(f_94, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.28/1.26  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.28/1.26  tff(f_110, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.28/1.26  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.28/1.26  tff(f_92, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.28/1.26  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.26  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.28/1.26  tff(c_62, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.28/1.26  tff(c_65, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_62])).
% 2.28/1.26  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_65])).
% 2.28/1.26  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.28/1.26  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.28/1.26  tff(c_70, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.28/1.26  tff(c_74, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_70])).
% 2.28/1.26  tff(c_82, plain, (![B_52, A_53]: (k1_relat_1(B_52)=A_53 | ~v1_partfun1(B_52, A_53) | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.26  tff(c_85, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_82])).
% 2.28/1.26  tff(c_88, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_85])).
% 2.28/1.26  tff(c_89, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_88])).
% 2.28/1.26  tff(c_42, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.28/1.26  tff(c_103, plain, (![C_61, A_62, B_63]: (v1_partfun1(C_61, A_62) | ~v1_funct_2(C_61, A_62, B_63) | ~v1_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | v1_xboole_0(B_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.28/1.26  tff(c_106, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_103])).
% 2.28/1.26  tff(c_109, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_106])).
% 2.28/1.26  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_89, c_109])).
% 2.28/1.26  tff(c_112, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_88])).
% 2.28/1.26  tff(c_30, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.28/1.26  tff(c_10, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.26  tff(c_133, plain, (![B_69]: (r2_hidden('#skF_1'(k1_relat_1(B_69), B_69), k1_relat_1(B_69)) | k6_partfun1(k1_relat_1(B_69))=B_69 | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 2.28/1.26  tff(c_139, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_133])).
% 2.28/1.26  tff(c_145, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44, c_112, c_112, c_139])).
% 2.28/1.26  tff(c_148, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_145])).
% 2.28/1.26  tff(c_36, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.28/1.26  tff(c_149, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_36])).
% 2.28/1.26  tff(c_163, plain, (![A_70, B_71, D_72]: (r2_funct_2(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(D_72, A_70, B_71) | ~v1_funct_1(D_72))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.28/1.26  tff(c_165, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_163])).
% 2.28/1.26  tff(c_168, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_165])).
% 2.28/1.26  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_168])).
% 2.28/1.26  tff(c_172, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_145])).
% 2.28/1.26  tff(c_8, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.26  tff(c_206, plain, (![B_77]: (k1_funct_1(B_77, '#skF_1'(k1_relat_1(B_77), B_77))!='#skF_1'(k1_relat_1(B_77), B_77) | k6_partfun1(k1_relat_1(B_77))=B_77 | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8])).
% 2.28/1.26  tff(c_209, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_206])).
% 2.28/1.26  tff(c_211, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44, c_112, c_112, c_209])).
% 2.28/1.26  tff(c_212, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_172, c_211])).
% 2.28/1.26  tff(c_171, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_145])).
% 2.28/1.26  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.26  tff(c_176, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_171, c_2])).
% 2.28/1.26  tff(c_38, plain, (![C_35]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_35)=C_35 | ~m1_subset_1(C_35, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.28/1.26  tff(c_180, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_176, c_38])).
% 2.28/1.26  tff(c_213, plain, (![A_78, B_79, C_80, D_81]: (k3_funct_2(A_78, B_79, C_80, D_81)=k1_funct_1(C_80, D_81) | ~m1_subset_1(D_81, A_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(C_80, A_78, B_79) | ~v1_funct_1(C_80) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.28/1.26  tff(c_217, plain, (![B_79, C_80]: (k3_funct_2('#skF_2', B_79, C_80, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_80, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_79))) | ~v1_funct_2(C_80, '#skF_2', B_79) | ~v1_funct_1(C_80) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_176, c_213])).
% 2.28/1.26  tff(c_225, plain, (![B_82, C_83]: (k3_funct_2('#skF_2', B_82, C_83, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_83, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_82))) | ~v1_funct_2(C_83, '#skF_2', B_82) | ~v1_funct_1(C_83))), inference(negUnitSimplification, [status(thm)], [c_46, c_217])).
% 2.28/1.26  tff(c_228, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_225])).
% 2.28/1.26  tff(c_231, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_180, c_228])).
% 2.28/1.26  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_231])).
% 2.28/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  Inference rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Ref     : 0
% 2.28/1.26  #Sup     : 33
% 2.28/1.26  #Fact    : 0
% 2.28/1.26  #Define  : 0
% 2.28/1.26  #Split   : 2
% 2.28/1.26  #Chain   : 0
% 2.28/1.26  #Close   : 0
% 2.28/1.26  
% 2.28/1.26  Ordering : KBO
% 2.28/1.26  
% 2.28/1.26  Simplification rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Subsume      : 0
% 2.28/1.26  #Demod        : 61
% 2.28/1.26  #Tautology    : 15
% 2.28/1.26  #SimpNegUnit  : 9
% 2.28/1.26  #BackRed      : 1
% 2.28/1.26  
% 2.28/1.26  #Partial instantiations: 0
% 2.28/1.26  #Strategies tried      : 1
% 2.28/1.26  
% 2.28/1.26  Timing (in seconds)
% 2.28/1.26  ----------------------
% 2.28/1.26  Preprocessing        : 0.31
% 2.28/1.26  Parsing              : 0.16
% 2.28/1.26  CNF conversion       : 0.02
% 2.28/1.26  Main loop            : 0.19
% 2.28/1.26  Inferencing          : 0.07
% 2.28/1.26  Reduction            : 0.06
% 2.28/1.26  Demodulation         : 0.04
% 2.28/1.27  BG Simplification    : 0.01
% 2.28/1.27  Subsumption          : 0.02
% 2.28/1.27  Abstraction          : 0.01
% 2.28/1.27  MUC search           : 0.00
% 2.28/1.27  Cooper               : 0.00
% 2.28/1.27  Total                : 0.53
% 2.28/1.27  Index Insertion      : 0.00
% 2.28/1.27  Index Deletion       : 0.00
% 2.28/1.27  Index Matching       : 0.00
% 2.28/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
