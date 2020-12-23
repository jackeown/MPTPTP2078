%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:24 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :  246 (9490 expanded)
%              Number of leaves         :   54 (3309 expanded)
%              Depth                    :   27
%              Number of atoms          :  436 (28277 expanded)
%              Number of equality atoms :  122 (8817 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_161,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_70,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_82,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_90,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_82])).

tff(c_89,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_82])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_146,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_89,c_64])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( v1_relat_1(B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_2))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_146,c_6])).

tff(c_152,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) = k1_xboole_0
      | k1_relat_1(A_9) != k1_xboole_0
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_152,c_16])).

tff(c_161,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1179,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_relset_1(A_152,B_153,C_154) = k2_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1183,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_146,c_1179])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_131,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_89,c_62])).

tff(c_1184,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_131])).

tff(c_54,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(k2_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1199,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_54])).

tff(c_1203,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1199])).

tff(c_1204,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1203])).

tff(c_1131,plain,(
    ! [C_141,A_142,B_143] :
      ( v4_relat_1(C_141,A_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1135,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_146,c_1131])).

tff(c_1148,plain,(
    ! [B_146,A_147] :
      ( k1_relat_1(B_146) = A_147
      | ~ v1_partfun1(B_146,A_147)
      | ~ v4_relat_1(B_146,A_147)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1151,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1135,c_1148])).

tff(c_1154,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1151])).

tff(c_1155,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1154])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_91,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_66])).

tff(c_100,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_91])).

tff(c_1194,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_100])).

tff(c_1193,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_146])).

tff(c_1373,plain,(
    ! [C_170,A_171,B_172] :
      ( v1_partfun1(C_170,A_171)
      | ~ v1_funct_2(C_170,A_171,B_172)
      | ~ v1_funct_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | v1_xboole_0(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1382,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1193,c_1373])).

tff(c_1387,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1194,c_1382])).

tff(c_1389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1204,c_1155,c_1387])).

tff(c_1390,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1154])).

tff(c_1394,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_146])).

tff(c_1446,plain,(
    ! [A_173,B_174,C_175] :
      ( k2_relset_1(A_173,B_174,C_175) = k2_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1450,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1394,c_1446])).

tff(c_1395,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_131])).

tff(c_1451,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_1395])).

tff(c_1457,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1394])).

tff(c_1137,plain,(
    ! [A_145] :
      ( k4_relat_1(A_145) = k2_funct_1(A_145)
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1140,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1137])).

tff(c_1143,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_68,c_1140])).

tff(c_1500,plain,(
    ! [A_176,B_177,C_178] :
      ( k3_relset_1(A_176,B_177,C_178) = k4_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1503,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1457,c_1500])).

tff(c_1505,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1503])).

tff(c_1577,plain,(
    ! [A_190,B_191,C_192] :
      ( m1_subset_1(k3_relset_1(A_190,B_191,C_192),k1_zfmisc_1(k2_zfmisc_1(B_191,A_190)))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1598,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_1577])).

tff(c_1608,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1457,c_1598])).

tff(c_1626,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1608,c_6])).

tff(c_1634,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1626])).

tff(c_28,plain,(
    ! [C_16,A_14,B_15] :
      ( v4_relat_1(C_16,A_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1630,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1608,c_28])).

tff(c_44,plain,(
    ! [B_34,A_33] :
      ( k1_relat_1(B_34) = A_33
      | ~ v1_partfun1(B_34,A_33)
      | ~ v4_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1645,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1630,c_44])).

tff(c_1648,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1645])).

tff(c_1703,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1648])).

tff(c_1396,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_100])).

tff(c_1458,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1396])).

tff(c_1456,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1450])).

tff(c_1793,plain,(
    ! [C_202,B_203,A_204] :
      ( v1_funct_2(k2_funct_1(C_202),B_203,A_204)
      | k2_relset_1(A_204,B_203,C_202) != B_203
      | ~ v2_funct_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_2(C_202,A_204,B_203)
      | ~ v1_funct_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1805,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1457,c_1793])).

tff(c_1813,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1458,c_60,c_1456,c_1805])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1401,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_54])).

tff(c_1405,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1401])).

tff(c_1425,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1405])).

tff(c_1658,plain,(
    ! [C_193,A_194,B_195] :
      ( v1_partfun1(C_193,A_194)
      | ~ v1_funct_2(C_193,A_194,B_195)
      | ~ v1_funct_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | v1_xboole_0(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1661,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1608,c_1658])).

tff(c_1670,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1425,c_1661])).

tff(c_1693,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1670])).

tff(c_1696,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1693])).

tff(c_1700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_68,c_1696])).

tff(c_1701,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_1862,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1813,c_1701])).

tff(c_1863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1703,c_1862])).

tff(c_1864,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1648])).

tff(c_10,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1891,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_10])).

tff(c_1897,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1891])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(k2_funct_1(B_13),A_12) = k10_relat_1(B_13,A_12)
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1907,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_24])).

tff(c_1914,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_68,c_60,c_1907])).

tff(c_12,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1921,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1914,c_12])).

tff(c_1928,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1921])).

tff(c_34,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1629,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1608,c_34])).

tff(c_1934,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_1629])).

tff(c_2074,plain,(
    ! [A_217,B_218,C_219] :
      ( k2_tops_2(A_217,B_218,C_219) = k2_funct_1(C_219)
      | ~ v2_funct_1(C_219)
      | k2_relset_1(A_217,B_218,C_219) != B_218
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_2(C_219,A_217,B_218)
      | ~ v1_funct_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2086,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1457,c_2074])).

tff(c_2094,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1458,c_1456,c_60,c_2086])).

tff(c_224,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_228,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_146,c_224])).

tff(c_229,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_131])).

tff(c_249,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_54])).

tff(c_253,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_249])).

tff(c_254,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_253])).

tff(c_170,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_174,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_146,c_170])).

tff(c_187,plain,(
    ! [B_68,A_69] :
      ( k1_relat_1(B_68) = A_69
      | ~ v1_partfun1(B_68,A_69)
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_190,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_187])).

tff(c_193,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_190])).

tff(c_194,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_244,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_100])).

tff(c_243,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_146])).

tff(c_414,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_partfun1(C_92,A_93)
      | ~ v1_funct_2(C_92,A_93,B_94)
      | ~ v1_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | v1_xboole_0(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_423,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_243,c_414])).

tff(c_428,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_244,c_423])).

tff(c_430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_194,c_428])).

tff(c_431,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_434,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_146])).

tff(c_515,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_519,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_434,c_515])).

tff(c_435,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_131])).

tff(c_520,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_435])).

tff(c_528,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_434])).

tff(c_175,plain,(
    ! [A_66] :
      ( k4_relat_1(A_66) = k2_funct_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_178,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_175])).

tff(c_181,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_68,c_178])).

tff(c_36,plain,(
    ! [A_26,B_27,C_28] :
      ( k3_relset_1(A_26,B_27,C_28) = k4_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_553,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_528,c_36])).

tff(c_570,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_553])).

tff(c_633,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1(k3_relset_1(A_114,B_115,C_116),k1_zfmisc_1(k2_zfmisc_1(B_115,A_114)))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_654,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_633])).

tff(c_664,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_654])).

tff(c_682,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_664,c_6])).

tff(c_690,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_682])).

tff(c_686,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_664,c_28])).

tff(c_701,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_686,c_44])).

tff(c_704,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_701])).

tff(c_748,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_436,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_100])).

tff(c_529,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_436])).

tff(c_525,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_519])).

tff(c_795,plain,(
    ! [C_120,A_121,B_122] :
      ( v1_funct_1(k2_funct_1(C_120))
      | k2_relset_1(A_121,B_122,C_120) != B_122
      | ~ v2_funct_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_2(C_120,A_121,B_122)
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_807,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_528,c_795])).

tff(c_814,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_529,c_60,c_525,c_807])).

tff(c_845,plain,(
    ! [C_126,B_127,A_128] :
      ( v1_funct_2(k2_funct_1(C_126),B_127,A_128)
      | k2_relset_1(A_128,B_127,C_126) != B_127
      | ~ v2_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_2(C_126,A_128,B_127)
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_857,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_528,c_845])).

tff(c_865,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_529,c_60,c_525,c_857])).

tff(c_441,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_54])).

tff(c_445,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_441])).

tff(c_465,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_706,plain,(
    ! [C_117,A_118,B_119] :
      ( v1_partfun1(C_117,A_118)
      | ~ v1_funct_2(C_117,A_118,B_119)
      | ~ v1_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | v1_xboole_0(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_709,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_664,c_706])).

tff(c_718,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_709])).

tff(c_882,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_865,c_718])).

tff(c_883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_748,c_882])).

tff(c_884,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_32,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relset_1(A_20,B_21,C_22) = k1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_685,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_664,c_32])).

tff(c_886,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_685])).

tff(c_1095,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_tops_2(A_138,B_139,C_140) = k2_funct_1(C_140)
      | ~ v2_funct_1(C_140)
      | k2_relset_1(A_138,B_139,C_140) != B_139
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_2(C_140,A_138,B_139)
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1107,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_528,c_1095])).

tff(c_1115,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_529,c_525,c_60,c_1107])).

tff(c_58,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_168,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_89,c_89,c_90,c_90,c_89,c_89,c_58])).

tff(c_169,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_514,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_431,c_169])).

tff(c_526,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_520,c_520,c_514])).

tff(c_1116,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_526])).

tff(c_1119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_1116])).

tff(c_1121,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1124,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1121,c_4])).

tff(c_1128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_1124])).

tff(c_1129,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_1393,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_1390,c_1390,c_1129])).

tff(c_1649,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1451,c_1393])).

tff(c_2095,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2094,c_1649])).

tff(c_2099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_2095])).

tff(c_2101,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1405])).

tff(c_2104,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2101,c_4])).

tff(c_2108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_2104])).

tff(c_2109,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_2207,plain,(
    ! [A_237,B_238,C_239] :
      ( k2_relset_1(A_237,B_238,C_239) = k2_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2210,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_146,c_2207])).

tff(c_2212,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2109,c_2210])).

tff(c_2213,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2212,c_131])).

tff(c_2228,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2213,c_54])).

tff(c_2232,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2,c_2228])).

tff(c_2234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.14  
% 5.28/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.28/2.15  
% 5.28/2.15  %Foreground sorts:
% 5.28/2.15  
% 5.28/2.15  
% 5.28/2.15  %Background operators:
% 5.28/2.15  
% 5.28/2.15  
% 5.28/2.15  %Foreground operators:
% 5.28/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.28/2.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.28/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.28/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.28/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.28/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.28/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.28/2.15  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 5.28/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.28/2.15  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.28/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.28/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.28/2.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.28/2.15  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.28/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.28/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.28/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.28/2.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.28/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.28/2.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.28/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.28/2.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.28/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.28/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.28/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.28/2.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.28/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.28/2.15  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.28/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.28/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.28/2.15  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.28/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.28/2.15  
% 5.28/2.18  tff(f_185, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 5.28/2.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.28/2.18  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.28/2.18  tff(f_141, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.28/2.18  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.28/2.18  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 5.28/2.18  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.28/2.18  tff(f_149, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.28/2.18  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.28/2.18  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.28/2.18  tff(f_113, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.28/2.18  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 5.28/2.18  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 5.28/2.18  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 5.28/2.18  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.28/2.18  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.28/2.18  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.28/2.18  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 5.28/2.18  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.28/2.18  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.28/2.18  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.28/2.18  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.28/2.18  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_70, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.28/2.18  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.28/2.18  tff(c_74, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_82, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.28/2.18  tff(c_90, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_82])).
% 5.28/2.18  tff(c_89, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_82])).
% 5.28/2.18  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_146, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_89, c_64])).
% 5.28/2.18  tff(c_6, plain, (![B_4, A_2]: (v1_relat_1(B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_2)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.28/2.18  tff(c_149, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_146, c_6])).
% 5.28/2.18  tff(c_152, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_149])).
% 5.28/2.18  tff(c_16, plain, (![A_9]: (k2_relat_1(A_9)=k1_xboole_0 | k1_relat_1(A_9)!=k1_xboole_0 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.28/2.18  tff(c_159, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_152, c_16])).
% 5.28/2.18  tff(c_161, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_159])).
% 5.28/2.18  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_1179, plain, (![A_152, B_153, C_154]: (k2_relset_1(A_152, B_153, C_154)=k2_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.28/2.18  tff(c_1183, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_146, c_1179])).
% 5.28/2.18  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_131, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_89, c_62])).
% 5.28/2.18  tff(c_1184, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_131])).
% 5.28/2.18  tff(c_54, plain, (![A_39]: (~v1_xboole_0(k2_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.28/2.18  tff(c_1199, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1184, c_54])).
% 5.28/2.18  tff(c_1203, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1199])).
% 5.28/2.18  tff(c_1204, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1203])).
% 5.28/2.18  tff(c_1131, plain, (![C_141, A_142, B_143]: (v4_relat_1(C_141, A_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.28/2.18  tff(c_1135, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_146, c_1131])).
% 5.28/2.18  tff(c_1148, plain, (![B_146, A_147]: (k1_relat_1(B_146)=A_147 | ~v1_partfun1(B_146, A_147) | ~v4_relat_1(B_146, A_147) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.28/2.18  tff(c_1151, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1135, c_1148])).
% 5.28/2.18  tff(c_1154, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1151])).
% 5.28/2.18  tff(c_1155, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1154])).
% 5.28/2.18  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_91, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_66])).
% 5.28/2.18  tff(c_100, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_91])).
% 5.28/2.18  tff(c_1194, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_100])).
% 5.28/2.18  tff(c_1193, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_146])).
% 5.28/2.18  tff(c_1373, plain, (![C_170, A_171, B_172]: (v1_partfun1(C_170, A_171) | ~v1_funct_2(C_170, A_171, B_172) | ~v1_funct_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | v1_xboole_0(B_172))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.28/2.18  tff(c_1382, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1193, c_1373])).
% 5.28/2.18  tff(c_1387, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1194, c_1382])).
% 5.28/2.18  tff(c_1389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1204, c_1155, c_1387])).
% 5.28/2.18  tff(c_1390, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1154])).
% 5.28/2.18  tff(c_1394, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_146])).
% 5.28/2.18  tff(c_1446, plain, (![A_173, B_174, C_175]: (k2_relset_1(A_173, B_174, C_175)=k2_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.28/2.18  tff(c_1450, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1394, c_1446])).
% 5.28/2.18  tff(c_1395, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_131])).
% 5.28/2.18  tff(c_1451, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_1395])).
% 5.28/2.18  tff(c_1457, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1394])).
% 5.28/2.18  tff(c_1137, plain, (![A_145]: (k4_relat_1(A_145)=k2_funct_1(A_145) | ~v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.28/2.18  tff(c_1140, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1137])).
% 5.28/2.18  tff(c_1143, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_68, c_1140])).
% 5.28/2.18  tff(c_1500, plain, (![A_176, B_177, C_178]: (k3_relset_1(A_176, B_177, C_178)=k4_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.28/2.18  tff(c_1503, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1457, c_1500])).
% 5.28/2.18  tff(c_1505, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1503])).
% 5.28/2.18  tff(c_1577, plain, (![A_190, B_191, C_192]: (m1_subset_1(k3_relset_1(A_190, B_191, C_192), k1_zfmisc_1(k2_zfmisc_1(B_191, A_190))) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.28/2.18  tff(c_1598, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_1577])).
% 5.28/2.18  tff(c_1608, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1457, c_1598])).
% 5.28/2.18  tff(c_1626, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_1608, c_6])).
% 5.28/2.18  tff(c_1634, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1626])).
% 5.28/2.18  tff(c_28, plain, (![C_16, A_14, B_15]: (v4_relat_1(C_16, A_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.28/2.18  tff(c_1630, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1608, c_28])).
% 5.28/2.18  tff(c_44, plain, (![B_34, A_33]: (k1_relat_1(B_34)=A_33 | ~v1_partfun1(B_34, A_33) | ~v4_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.28/2.18  tff(c_1645, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1630, c_44])).
% 5.28/2.18  tff(c_1648, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1645])).
% 5.28/2.18  tff(c_1703, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1648])).
% 5.28/2.18  tff(c_1396, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_100])).
% 5.28/2.18  tff(c_1458, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1396])).
% 5.28/2.18  tff(c_1456, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1450])).
% 5.28/2.18  tff(c_1793, plain, (![C_202, B_203, A_204]: (v1_funct_2(k2_funct_1(C_202), B_203, A_204) | k2_relset_1(A_204, B_203, C_202)!=B_203 | ~v2_funct_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_2(C_202, A_204, B_203) | ~v1_funct_1(C_202))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.28/2.18  tff(c_1805, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1457, c_1793])).
% 5.28/2.18  tff(c_1813, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1458, c_60, c_1456, c_1805])).
% 5.28/2.18  tff(c_20, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.28/2.18  tff(c_1401, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1390, c_54])).
% 5.28/2.18  tff(c_1405, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1401])).
% 5.28/2.18  tff(c_1425, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1405])).
% 5.28/2.18  tff(c_1658, plain, (![C_193, A_194, B_195]: (v1_partfun1(C_193, A_194) | ~v1_funct_2(C_193, A_194, B_195) | ~v1_funct_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | v1_xboole_0(B_195))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.28/2.18  tff(c_1661, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1608, c_1658])).
% 5.28/2.18  tff(c_1670, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1425, c_1661])).
% 5.28/2.18  tff(c_1693, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1670])).
% 5.28/2.18  tff(c_1696, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1693])).
% 5.28/2.18  tff(c_1700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_68, c_1696])).
% 5.28/2.18  tff(c_1701, plain, (~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1670])).
% 5.28/2.18  tff(c_1862, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1813, c_1701])).
% 5.28/2.18  tff(c_1863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1703, c_1862])).
% 5.28/2.18  tff(c_1864, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1648])).
% 5.28/2.18  tff(c_10, plain, (![A_7]: (k9_relat_1(A_7, k1_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.28/2.18  tff(c_1891, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1864, c_10])).
% 5.28/2.18  tff(c_1897, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1891])).
% 5.28/2.18  tff(c_24, plain, (![B_13, A_12]: (k9_relat_1(k2_funct_1(B_13), A_12)=k10_relat_1(B_13, A_12) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.28/2.18  tff(c_1907, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1897, c_24])).
% 5.28/2.18  tff(c_1914, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_68, c_60, c_1907])).
% 5.28/2.18  tff(c_12, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.28/2.18  tff(c_1921, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1914, c_12])).
% 5.28/2.18  tff(c_1928, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1921])).
% 5.28/2.18  tff(c_34, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.28/2.18  tff(c_1629, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1608, c_34])).
% 5.28/2.18  tff(c_1934, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_1629])).
% 5.28/2.18  tff(c_2074, plain, (![A_217, B_218, C_219]: (k2_tops_2(A_217, B_218, C_219)=k2_funct_1(C_219) | ~v2_funct_1(C_219) | k2_relset_1(A_217, B_218, C_219)!=B_218 | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_2(C_219, A_217, B_218) | ~v1_funct_1(C_219))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.28/2.18  tff(c_2086, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1457, c_2074])).
% 5.28/2.18  tff(c_2094, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1458, c_1456, c_60, c_2086])).
% 5.28/2.18  tff(c_224, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.28/2.18  tff(c_228, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_146, c_224])).
% 5.28/2.18  tff(c_229, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_131])).
% 5.28/2.18  tff(c_249, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_229, c_54])).
% 5.28/2.18  tff(c_253, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_249])).
% 5.28/2.18  tff(c_254, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_253])).
% 5.28/2.18  tff(c_170, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.28/2.18  tff(c_174, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_146, c_170])).
% 5.28/2.18  tff(c_187, plain, (![B_68, A_69]: (k1_relat_1(B_68)=A_69 | ~v1_partfun1(B_68, A_69) | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.28/2.18  tff(c_190, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_174, c_187])).
% 5.28/2.18  tff(c_193, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_190])).
% 5.28/2.18  tff(c_194, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_193])).
% 5.28/2.18  tff(c_244, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_100])).
% 5.28/2.18  tff(c_243, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_146])).
% 5.28/2.18  tff(c_414, plain, (![C_92, A_93, B_94]: (v1_partfun1(C_92, A_93) | ~v1_funct_2(C_92, A_93, B_94) | ~v1_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | v1_xboole_0(B_94))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.28/2.18  tff(c_423, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_243, c_414])).
% 5.28/2.18  tff(c_428, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_244, c_423])).
% 5.28/2.18  tff(c_430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_194, c_428])).
% 5.28/2.18  tff(c_431, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_193])).
% 5.28/2.18  tff(c_434, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_146])).
% 5.28/2.18  tff(c_515, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.28/2.18  tff(c_519, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_434, c_515])).
% 5.28/2.18  tff(c_435, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_131])).
% 5.28/2.18  tff(c_520, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_435])).
% 5.28/2.18  tff(c_528, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_520, c_434])).
% 5.28/2.18  tff(c_175, plain, (![A_66]: (k4_relat_1(A_66)=k2_funct_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.28/2.18  tff(c_178, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_175])).
% 5.28/2.18  tff(c_181, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_68, c_178])).
% 5.28/2.18  tff(c_36, plain, (![A_26, B_27, C_28]: (k3_relset_1(A_26, B_27, C_28)=k4_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.28/2.18  tff(c_553, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_528, c_36])).
% 5.28/2.18  tff(c_570, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_553])).
% 5.28/2.18  tff(c_633, plain, (![A_114, B_115, C_116]: (m1_subset_1(k3_relset_1(A_114, B_115, C_116), k1_zfmisc_1(k2_zfmisc_1(B_115, A_114))) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.28/2.18  tff(c_654, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_570, c_633])).
% 5.28/2.18  tff(c_664, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_654])).
% 5.28/2.18  tff(c_682, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_664, c_6])).
% 5.28/2.18  tff(c_690, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_682])).
% 5.28/2.18  tff(c_686, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_664, c_28])).
% 5.28/2.18  tff(c_701, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_686, c_44])).
% 5.28/2.18  tff(c_704, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_701])).
% 5.28/2.18  tff(c_748, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_704])).
% 5.28/2.18  tff(c_436, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_100])).
% 5.28/2.18  tff(c_529, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_520, c_436])).
% 5.28/2.18  tff(c_525, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_519])).
% 5.28/2.18  tff(c_795, plain, (![C_120, A_121, B_122]: (v1_funct_1(k2_funct_1(C_120)) | k2_relset_1(A_121, B_122, C_120)!=B_122 | ~v2_funct_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_2(C_120, A_121, B_122) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.28/2.18  tff(c_807, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_528, c_795])).
% 5.28/2.18  tff(c_814, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_529, c_60, c_525, c_807])).
% 5.28/2.18  tff(c_845, plain, (![C_126, B_127, A_128]: (v1_funct_2(k2_funct_1(C_126), B_127, A_128) | k2_relset_1(A_128, B_127, C_126)!=B_127 | ~v2_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_2(C_126, A_128, B_127) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.28/2.18  tff(c_857, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_528, c_845])).
% 5.28/2.18  tff(c_865, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_529, c_60, c_525, c_857])).
% 5.28/2.18  tff(c_441, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_431, c_54])).
% 5.28/2.18  tff(c_445, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_441])).
% 5.28/2.18  tff(c_465, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_445])).
% 5.28/2.18  tff(c_706, plain, (![C_117, A_118, B_119]: (v1_partfun1(C_117, A_118) | ~v1_funct_2(C_117, A_118, B_119) | ~v1_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | v1_xboole_0(B_119))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.28/2.18  tff(c_709, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_664, c_706])).
% 5.28/2.18  tff(c_718, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_465, c_709])).
% 5.28/2.18  tff(c_882, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_865, c_718])).
% 5.28/2.18  tff(c_883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_748, c_882])).
% 5.28/2.18  tff(c_884, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_704])).
% 5.28/2.18  tff(c_32, plain, (![A_20, B_21, C_22]: (k1_relset_1(A_20, B_21, C_22)=k1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.28/2.18  tff(c_685, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_664, c_32])).
% 5.28/2.18  tff(c_886, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_884, c_685])).
% 5.28/2.18  tff(c_1095, plain, (![A_138, B_139, C_140]: (k2_tops_2(A_138, B_139, C_140)=k2_funct_1(C_140) | ~v2_funct_1(C_140) | k2_relset_1(A_138, B_139, C_140)!=B_139 | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_2(C_140, A_138, B_139) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.28/2.18  tff(c_1107, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_528, c_1095])).
% 5.28/2.18  tff(c_1115, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_529, c_525, c_60, c_1107])).
% 5.28/2.18  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.28/2.18  tff(c_168, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_89, c_89, c_90, c_90, c_89, c_89, c_58])).
% 5.28/2.18  tff(c_169, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_168])).
% 5.28/2.18  tff(c_514, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_431, c_169])).
% 5.28/2.18  tff(c_526, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_520, c_520, c_514])).
% 5.28/2.18  tff(c_1116, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_526])).
% 5.28/2.18  tff(c_1119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_1116])).
% 5.28/2.18  tff(c_1121, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_445])).
% 5.28/2.18  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.28/2.18  tff(c_1124, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1121, c_4])).
% 5.28/2.18  tff(c_1128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_1124])).
% 5.28/2.18  tff(c_1129, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_168])).
% 5.28/2.18  tff(c_1393, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_1390, c_1390, c_1129])).
% 5.28/2.18  tff(c_1649, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1451, c_1393])).
% 5.28/2.18  tff(c_2095, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2094, c_1649])).
% 5.28/2.18  tff(c_2099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1934, c_2095])).
% 5.28/2.18  tff(c_2101, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1405])).
% 5.28/2.18  tff(c_2104, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2101, c_4])).
% 5.28/2.18  tff(c_2108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_2104])).
% 5.28/2.18  tff(c_2109, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_159])).
% 5.28/2.18  tff(c_2207, plain, (![A_237, B_238, C_239]: (k2_relset_1(A_237, B_238, C_239)=k2_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.28/2.18  tff(c_2210, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_146, c_2207])).
% 5.28/2.18  tff(c_2212, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2109, c_2210])).
% 5.28/2.18  tff(c_2213, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2212, c_131])).
% 5.28/2.18  tff(c_2228, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2213, c_54])).
% 5.28/2.18  tff(c_2232, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2, c_2228])).
% 5.28/2.18  tff(c_2234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2232])).
% 5.28/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.18  
% 5.28/2.18  Inference rules
% 5.28/2.18  ----------------------
% 5.28/2.18  #Ref     : 0
% 5.28/2.18  #Sup     : 495
% 5.28/2.18  #Fact    : 0
% 5.28/2.18  #Define  : 0
% 5.28/2.18  #Split   : 21
% 5.28/2.18  #Chain   : 0
% 5.28/2.18  #Close   : 0
% 5.28/2.18  
% 5.28/2.18  Ordering : KBO
% 5.28/2.18  
% 5.28/2.18  Simplification rules
% 5.28/2.18  ----------------------
% 5.28/2.18  #Subsume      : 15
% 5.28/2.18  #Demod        : 390
% 5.28/2.18  #Tautology    : 248
% 5.28/2.18  #SimpNegUnit  : 30
% 5.28/2.18  #BackRed      : 65
% 5.28/2.18  
% 5.28/2.18  #Partial instantiations: 0
% 5.28/2.18  #Strategies tried      : 1
% 5.28/2.18  
% 5.28/2.18  Timing (in seconds)
% 5.28/2.18  ----------------------
% 5.28/2.19  Preprocessing        : 0.58
% 5.28/2.19  Parsing              : 0.31
% 5.28/2.19  CNF conversion       : 0.04
% 5.28/2.19  Main loop            : 0.72
% 5.28/2.19  Inferencing          : 0.25
% 5.28/2.19  Reduction            : 0.25
% 5.28/2.19  Demodulation         : 0.17
% 5.28/2.19  BG Simplification    : 0.04
% 5.28/2.19  Subsumption          : 0.12
% 5.28/2.19  Abstraction          : 0.04
% 5.28/2.19  MUC search           : 0.00
% 5.28/2.19  Cooper               : 0.00
% 5.28/2.19  Total                : 1.39
% 5.28/2.19  Index Insertion      : 0.00
% 5.28/2.19  Index Deletion       : 0.00
% 5.28/2.19  Index Matching       : 0.00
% 5.28/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
