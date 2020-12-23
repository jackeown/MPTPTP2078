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
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 128 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 ( 358 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    ! [C_32,B_31] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_32),B_31,C_32),k1_relat_1(C_32))
      | m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_32),B_31)))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_12,plain,(
    ! [B_12,C_14,A_11] :
      ( r2_hidden(k1_funct_1(B_12,C_14),A_11)
      | ~ r2_hidden(C_14,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_634,plain,(
    ! [C_171,B_172] :
      ( ~ r2_hidden(k1_funct_1(C_171,'#skF_1'(k1_relat_1(C_171),B_172,C_171)),B_172)
      | m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_171),B_172)))
      | ~ v1_funct_1(C_171)
      | ~ v1_relat_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_894,plain,(
    ! [B_191,A_192] :
      ( m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_191),A_192)))
      | ~ r2_hidden('#skF_1'(k1_relat_1(B_191),A_192,B_191),k1_relat_1(B_191))
      | ~ v1_funct_1(B_191)
      | ~ v5_relat_1(B_191,A_192)
      | ~ v1_relat_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_12,c_634])).

tff(c_927,plain,(
    ! [C_197,B_198] :
      ( ~ v5_relat_1(C_197,B_198)
      | m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_197),B_198)))
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_32,c_894])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_974,plain,(
    ! [C_197,B_198] :
      ( r1_tarski(C_197,k2_zfmisc_1(k1_relat_1(C_197),B_198))
      | ~ v5_relat_1(C_197,B_198)
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_927,c_2])).

tff(c_20,plain,(
    ! [A_21,B_22,C_23] :
      ( k2_relset_1(A_21,B_22,C_23) = k2_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1090,plain,(
    ! [C_204,B_205] :
      ( k2_relset_1(k1_relat_1(C_204),B_205,C_204) = k2_relat_1(C_204)
      | ~ v5_relat_1(C_204,B_205)
      | ~ v1_funct_1(C_204)
      | ~ v1_relat_1(C_204) ) ),
    inference(resolution,[status(thm)],[c_927,c_20])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_332,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1(k2_relset_1(A_116,B_117,C_118),k1_zfmisc_1(B_117))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_398,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(k2_relset_1(A_122,B_123,C_124),B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(resolution,[status(thm)],[c_332,c_2])).

tff(c_408,plain,(
    ! [A_122,B_123,A_1] :
      ( r1_tarski(k2_relset_1(A_122,B_123,A_1),B_123)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_4,c_398])).

tff(c_1204,plain,(
    ! [C_220,B_221] :
      ( r1_tarski(k2_relat_1(C_220),B_221)
      | ~ r1_tarski(C_220,k2_zfmisc_1(k1_relat_1(C_220),B_221))
      | ~ v5_relat_1(C_220,B_221)
      | ~ v1_funct_1(C_220)
      | ~ v1_relat_1(C_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_408])).

tff(c_1266,plain,(
    ! [C_223,B_224] :
      ( r1_tarski(k2_relat_1(C_223),B_224)
      | ~ v5_relat_1(C_223,B_224)
      | ~ v1_funct_1(C_223)
      | ~ v1_relat_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_974,c_1204])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_68,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_86,plain,(
    ! [C_48,A_49,B_50] :
      ( v4_relat_1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_119,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(B_61) = A_62
      | ~ v1_partfun1(B_61,A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_122,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_119])).

tff(c_125,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_122])).

tff(c_126,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_281,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_partfun1(C_107,A_108)
      | ~ v1_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | v1_xboole_0(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_292,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_281])).

tff(c_297,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_292])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_126,c_297])).

tff(c_300,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_373,plain,(
    ! [A_119,B_120] :
      ( k1_relat_1(k5_relat_1(A_119,B_120)) = k1_relat_1(A_119)
      | ~ r1_tarski(k2_relat_1(A_119),k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_376,plain,(
    ! [A_119] :
      ( k1_relat_1(k5_relat_1(A_119,'#skF_3')) = k1_relat_1(A_119)
      | ~ r1_tarski(k2_relat_1(A_119),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_373])).

tff(c_378,plain,(
    ! [A_119] :
      ( k1_relat_1(k5_relat_1(A_119,'#skF_3')) = k1_relat_1(A_119)
      | ~ r1_tarski(k2_relat_1(A_119),'#skF_2')
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_376])).

tff(c_1343,plain,(
    ! [C_229] :
      ( k1_relat_1(k5_relat_1(C_229,'#skF_3')) = k1_relat_1(C_229)
      | ~ v5_relat_1(C_229,'#skF_2')
      | ~ v1_funct_1(C_229)
      | ~ v1_relat_1(C_229) ) ),
    inference(resolution,[status(thm)],[c_1266,c_378])).

tff(c_42,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) != k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1394,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1343,c_42])).

tff(c_1407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_1394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:01:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.57  
% 3.43/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.43/1.57  
% 3.43/1.57  %Foreground sorts:
% 3.43/1.57  
% 3.43/1.57  
% 3.43/1.57  %Background operators:
% 3.43/1.57  
% 3.43/1.57  
% 3.43/1.57  %Foreground operators:
% 3.43/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.43/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.43/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.43/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.57  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.43/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.43/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.43/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.43/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.57  
% 3.61/1.59  tff(f_131, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 3.61/1.59  tff(f_111, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 3.61/1.59  tff(f_58, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.61/1.59  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.61/1.59  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.61/1.59  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.61/1.59  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.61/1.59  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.61/1.59  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.61/1.59  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.61/1.59  tff(f_86, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.61/1.59  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.61/1.59  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_46, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_32, plain, (![C_32, B_31]: (r2_hidden('#skF_1'(k1_relat_1(C_32), B_31, C_32), k1_relat_1(C_32)) | m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_32), B_31))) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.61/1.59  tff(c_12, plain, (![B_12, C_14, A_11]: (r2_hidden(k1_funct_1(B_12, C_14), A_11) | ~r2_hidden(C_14, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.61/1.59  tff(c_634, plain, (![C_171, B_172]: (~r2_hidden(k1_funct_1(C_171, '#skF_1'(k1_relat_1(C_171), B_172, C_171)), B_172) | m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_171), B_172))) | ~v1_funct_1(C_171) | ~v1_relat_1(C_171))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.61/1.59  tff(c_894, plain, (![B_191, A_192]: (m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_191), A_192))) | ~r2_hidden('#skF_1'(k1_relat_1(B_191), A_192, B_191), k1_relat_1(B_191)) | ~v1_funct_1(B_191) | ~v5_relat_1(B_191, A_192) | ~v1_relat_1(B_191))), inference(resolution, [status(thm)], [c_12, c_634])).
% 3.61/1.59  tff(c_927, plain, (![C_197, B_198]: (~v5_relat_1(C_197, B_198) | m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_197), B_198))) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197))), inference(resolution, [status(thm)], [c_32, c_894])).
% 3.61/1.59  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.61/1.59  tff(c_974, plain, (![C_197, B_198]: (r1_tarski(C_197, k2_zfmisc_1(k1_relat_1(C_197), B_198)) | ~v5_relat_1(C_197, B_198) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197))), inference(resolution, [status(thm)], [c_927, c_2])).
% 3.61/1.59  tff(c_20, plain, (![A_21, B_22, C_23]: (k2_relset_1(A_21, B_22, C_23)=k2_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.59  tff(c_1090, plain, (![C_204, B_205]: (k2_relset_1(k1_relat_1(C_204), B_205, C_204)=k2_relat_1(C_204) | ~v5_relat_1(C_204, B_205) | ~v1_funct_1(C_204) | ~v1_relat_1(C_204))), inference(resolution, [status(thm)], [c_927, c_20])).
% 3.61/1.59  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.61/1.59  tff(c_332, plain, (![A_116, B_117, C_118]: (m1_subset_1(k2_relset_1(A_116, B_117, C_118), k1_zfmisc_1(B_117)) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.61/1.59  tff(c_398, plain, (![A_122, B_123, C_124]: (r1_tarski(k2_relset_1(A_122, B_123, C_124), B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(resolution, [status(thm)], [c_332, c_2])).
% 3.61/1.59  tff(c_408, plain, (![A_122, B_123, A_1]: (r1_tarski(k2_relset_1(A_122, B_123, A_1), B_123) | ~r1_tarski(A_1, k2_zfmisc_1(A_122, B_123)))), inference(resolution, [status(thm)], [c_4, c_398])).
% 3.61/1.59  tff(c_1204, plain, (![C_220, B_221]: (r1_tarski(k2_relat_1(C_220), B_221) | ~r1_tarski(C_220, k2_zfmisc_1(k1_relat_1(C_220), B_221)) | ~v5_relat_1(C_220, B_221) | ~v1_funct_1(C_220) | ~v1_relat_1(C_220))), inference(superposition, [status(thm), theory('equality')], [c_1090, c_408])).
% 3.61/1.59  tff(c_1266, plain, (![C_223, B_224]: (r1_tarski(k2_relat_1(C_223), B_224) | ~v5_relat_1(C_223, B_224) | ~v1_funct_1(C_223) | ~v1_relat_1(C_223))), inference(resolution, [status(thm)], [c_974, c_1204])).
% 3.61/1.59  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.61/1.59  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_68, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.61/1.59  tff(c_74, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_68])).
% 3.61/1.59  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_74])).
% 3.61/1.59  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_86, plain, (![C_48, A_49, B_50]: (v4_relat_1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.59  tff(c_95, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_86])).
% 3.61/1.59  tff(c_119, plain, (![B_61, A_62]: (k1_relat_1(B_61)=A_62 | ~v1_partfun1(B_61, A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.61/1.59  tff(c_122, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_95, c_119])).
% 3.61/1.59  tff(c_125, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_122])).
% 3.61/1.59  tff(c_126, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_125])).
% 3.61/1.59  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_281, plain, (![C_107, A_108, B_109]: (v1_partfun1(C_107, A_108) | ~v1_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | v1_xboole_0(B_109))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.59  tff(c_292, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_281])).
% 3.61/1.59  tff(c_297, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_292])).
% 3.61/1.59  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_126, c_297])).
% 3.61/1.59  tff(c_300, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_125])).
% 3.61/1.59  tff(c_373, plain, (![A_119, B_120]: (k1_relat_1(k5_relat_1(A_119, B_120))=k1_relat_1(A_119) | ~r1_tarski(k2_relat_1(A_119), k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.61/1.59  tff(c_376, plain, (![A_119]: (k1_relat_1(k5_relat_1(A_119, '#skF_3'))=k1_relat_1(A_119) | ~r1_tarski(k2_relat_1(A_119), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_300, c_373])).
% 3.61/1.59  tff(c_378, plain, (![A_119]: (k1_relat_1(k5_relat_1(A_119, '#skF_3'))=k1_relat_1(A_119) | ~r1_tarski(k2_relat_1(A_119), '#skF_2') | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_376])).
% 3.61/1.59  tff(c_1343, plain, (![C_229]: (k1_relat_1(k5_relat_1(C_229, '#skF_3'))=k1_relat_1(C_229) | ~v5_relat_1(C_229, '#skF_2') | ~v1_funct_1(C_229) | ~v1_relat_1(C_229))), inference(resolution, [status(thm)], [c_1266, c_378])).
% 3.61/1.59  tff(c_42, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))!=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.61/1.59  tff(c_1394, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1343, c_42])).
% 3.61/1.59  tff(c_1407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_1394])).
% 3.61/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.59  
% 3.61/1.59  Inference rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Ref     : 0
% 3.61/1.59  #Sup     : 289
% 3.61/1.59  #Fact    : 0
% 3.61/1.59  #Define  : 0
% 3.61/1.59  #Split   : 5
% 3.61/1.59  #Chain   : 0
% 3.61/1.59  #Close   : 0
% 3.61/1.59  
% 3.61/1.59  Ordering : KBO
% 3.61/1.59  
% 3.61/1.59  Simplification rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Subsume      : 81
% 3.61/1.59  #Demod        : 167
% 3.61/1.59  #Tautology    : 54
% 3.61/1.59  #SimpNegUnit  : 3
% 3.61/1.59  #BackRed      : 0
% 3.61/1.59  
% 3.61/1.59  #Partial instantiations: 0
% 3.61/1.59  #Strategies tried      : 1
% 3.61/1.59  
% 3.61/1.59  Timing (in seconds)
% 3.61/1.59  ----------------------
% 3.61/1.59  Preprocessing        : 0.33
% 3.61/1.59  Parsing              : 0.18
% 3.61/1.59  CNF conversion       : 0.02
% 3.61/1.59  Main loop            : 0.48
% 3.61/1.59  Inferencing          : 0.19
% 3.61/1.59  Reduction            : 0.15
% 3.61/1.59  Demodulation         : 0.10
% 3.61/1.59  BG Simplification    : 0.03
% 3.61/1.59  Subsumption          : 0.08
% 3.61/1.59  Abstraction          : 0.03
% 3.61/1.59  MUC search           : 0.00
% 3.61/1.59  Cooper               : 0.00
% 3.61/1.59  Total                : 0.85
% 3.61/1.59  Index Insertion      : 0.00
% 3.61/1.59  Index Deletion       : 0.00
% 3.61/1.59  Index Matching       : 0.00
% 3.61/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
