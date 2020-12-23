%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:20 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 365 expanded)
%              Number of leaves         :   32 ( 142 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 (1128 expanded)
%              Number of equality atoms :   47 ( 385 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_118,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_84,axiom,(
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

tff(f_100,axiom,(
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

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_82,axiom,(
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

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_63,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_71,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_84,plain,(
    ! [B_51,A_52,C_53] :
      ( k1_xboole_0 = B_51
      | k1_relset_1(A_52,B_51,C_53) = A_52
      | ~ v1_funct_2(C_53,A_52,B_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_84])).

tff(c_90,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_75,c_87])).

tff(c_91,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_32,plain,(
    ! [A_21] : k6_relat_1(A_21) = k6_partfun1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [B_54] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_54),B_54),k1_relat_1(B_54))
      | k6_partfun1(k1_relat_1(B_54)) = B_54
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_107,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_101])).

tff(c_113,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_46,c_91,c_91,c_107])).

tff(c_116,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_38,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_124,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_38])).

tff(c_151,plain,(
    ! [A_60,B_61,D_62] :
      ( r2_funct_2(A_60,B_61,D_62,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(D_62,A_60,B_61)
      | ~ v1_funct_1(D_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_153,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_151])).

tff(c_156,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_156])).

tff(c_160,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_6,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    ! [B_70] :
      ( k1_funct_1(B_70,'#skF_1'(k1_relat_1(B_70),B_70)) != '#skF_1'(k1_relat_1(B_70),B_70)
      | k6_partfun1(k1_relat_1(B_70)) = B_70
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_204,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_201])).

tff(c_206,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_46,c_91,c_91,c_204])).

tff(c_207,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_206])).

tff(c_159,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_164,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_4])).

tff(c_40,plain,(
    ! [C_30] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_30) = C_30
      | ~ m1_subset_1(C_30,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_168,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_40])).

tff(c_208,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k3_funct_2(A_71,B_72,C_73,D_74) = k1_funct_1(C_73,D_74)
      | ~ m1_subset_1(D_74,A_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_212,plain,(
    ! [B_72,C_73] :
      ( k3_funct_2('#skF_2',B_72,C_73,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_73,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_72)))
      | ~ v1_funct_2(C_73,'#skF_2',B_72)
      | ~ v1_funct_1(C_73)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_164,c_208])).

tff(c_220,plain,(
    ! [B_75,C_76] :
      ( k3_funct_2('#skF_2',B_75,C_76,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_76,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_75)))
      | ~ v1_funct_2(C_76,'#skF_2',B_75)
      | ~ v1_funct_1(C_76) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_212])).

tff(c_223,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_220])).

tff(c_226,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_168,c_223])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_226])).

tff(c_229,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_241,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_2])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.34  
% 2.15/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.34  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.15/1.34  
% 2.15/1.34  %Foreground sorts:
% 2.15/1.34  
% 2.15/1.34  
% 2.15/1.34  %Background operators:
% 2.15/1.34  
% 2.15/1.34  
% 2.15/1.34  %Foreground operators:
% 2.15/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.15/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.15/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.15/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.15/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.15/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.34  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.15/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.34  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.15/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.34  
% 2.46/1.36  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.46/1.36  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.36  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.36  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.46/1.36  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.46/1.36  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.46/1.36  tff(f_100, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.46/1.36  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.46/1.36  tff(f_82, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.46/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.46/1.36  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.46/1.36  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.46/1.36  tff(c_63, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.36  tff(c_67, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_63])).
% 2.46/1.36  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.46/1.36  tff(c_44, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.46/1.36  tff(c_71, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.36  tff(c_75, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_71])).
% 2.46/1.36  tff(c_84, plain, (![B_51, A_52, C_53]: (k1_xboole_0=B_51 | k1_relset_1(A_52, B_51, C_53)=A_52 | ~v1_funct_2(C_53, A_52, B_51) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.36  tff(c_87, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_84])).
% 2.46/1.36  tff(c_90, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_75, c_87])).
% 2.46/1.36  tff(c_91, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_90])).
% 2.46/1.36  tff(c_32, plain, (![A_21]: (k6_relat_1(A_21)=k6_partfun1(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.46/1.36  tff(c_8, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.36  tff(c_101, plain, (![B_54]: (r2_hidden('#skF_1'(k1_relat_1(B_54), B_54), k1_relat_1(B_54)) | k6_partfun1(k1_relat_1(B_54))=B_54 | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 2.46/1.36  tff(c_107, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_101])).
% 2.46/1.36  tff(c_113, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_46, c_91, c_91, c_107])).
% 2.46/1.36  tff(c_116, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_113])).
% 2.46/1.36  tff(c_38, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.46/1.36  tff(c_124, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_38])).
% 2.46/1.36  tff(c_151, plain, (![A_60, B_61, D_62]: (r2_funct_2(A_60, B_61, D_62, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(D_62, A_60, B_61) | ~v1_funct_1(D_62))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.46/1.36  tff(c_153, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_151])).
% 2.46/1.36  tff(c_156, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_153])).
% 2.46/1.36  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_156])).
% 2.46/1.36  tff(c_160, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_113])).
% 2.46/1.36  tff(c_6, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.36  tff(c_201, plain, (![B_70]: (k1_funct_1(B_70, '#skF_1'(k1_relat_1(B_70), B_70))!='#skF_1'(k1_relat_1(B_70), B_70) | k6_partfun1(k1_relat_1(B_70))=B_70 | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 2.46/1.36  tff(c_204, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_201])).
% 2.46/1.36  tff(c_206, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_46, c_91, c_91, c_204])).
% 2.46/1.36  tff(c_207, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_160, c_206])).
% 2.46/1.36  tff(c_159, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_113])).
% 2.46/1.36  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.46/1.36  tff(c_164, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_159, c_4])).
% 2.46/1.36  tff(c_40, plain, (![C_30]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_30)=C_30 | ~m1_subset_1(C_30, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.46/1.36  tff(c_168, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_164, c_40])).
% 2.46/1.36  tff(c_208, plain, (![A_71, B_72, C_73, D_74]: (k3_funct_2(A_71, B_72, C_73, D_74)=k1_funct_1(C_73, D_74) | ~m1_subset_1(D_74, A_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_73, A_71, B_72) | ~v1_funct_1(C_73) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.46/1.36  tff(c_212, plain, (![B_72, C_73]: (k3_funct_2('#skF_2', B_72, C_73, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_73, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_72))) | ~v1_funct_2(C_73, '#skF_2', B_72) | ~v1_funct_1(C_73) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_164, c_208])).
% 2.46/1.36  tff(c_220, plain, (![B_75, C_76]: (k3_funct_2('#skF_2', B_75, C_76, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_76, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_75))) | ~v1_funct_2(C_76, '#skF_2', B_75) | ~v1_funct_1(C_76))), inference(negUnitSimplification, [status(thm)], [c_48, c_212])).
% 2.46/1.36  tff(c_223, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_220])).
% 2.46/1.36  tff(c_226, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_168, c_223])).
% 2.46/1.36  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_226])).
% 2.46/1.36  tff(c_229, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_90])).
% 2.46/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.46/1.36  tff(c_241, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_2])).
% 2.46/1.36  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_241])).
% 2.46/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  
% 2.46/1.36  Inference rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Ref     : 0
% 2.46/1.36  #Sup     : 36
% 2.46/1.36  #Fact    : 0
% 2.46/1.36  #Define  : 0
% 2.46/1.36  #Split   : 2
% 2.46/1.36  #Chain   : 0
% 2.46/1.36  #Close   : 0
% 2.46/1.36  
% 2.46/1.36  Ordering : KBO
% 2.46/1.36  
% 2.46/1.36  Simplification rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Subsume      : 0
% 2.46/1.36  #Demod        : 85
% 2.46/1.36  #Tautology    : 21
% 2.46/1.36  #SimpNegUnit  : 8
% 2.46/1.36  #BackRed      : 8
% 2.46/1.36  
% 2.46/1.36  #Partial instantiations: 0
% 2.46/1.36  #Strategies tried      : 1
% 2.46/1.36  
% 2.46/1.36  Timing (in seconds)
% 2.46/1.36  ----------------------
% 2.46/1.36  Preprocessing        : 0.31
% 2.46/1.36  Parsing              : 0.16
% 2.46/1.36  CNF conversion       : 0.02
% 2.46/1.36  Main loop            : 0.21
% 2.46/1.36  Inferencing          : 0.07
% 2.46/1.36  Reduction            : 0.07
% 2.46/1.36  Demodulation         : 0.05
% 2.46/1.36  BG Simplification    : 0.02
% 2.46/1.36  Subsumption          : 0.03
% 2.46/1.36  Abstraction          : 0.01
% 2.46/1.36  MUC search           : 0.00
% 2.46/1.36  Cooper               : 0.00
% 2.46/1.36  Total                : 0.56
% 2.46/1.36  Index Insertion      : 0.00
% 2.46/1.36  Index Deletion       : 0.00
% 2.46/1.36  Index Matching       : 0.00
% 2.46/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
