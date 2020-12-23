%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:43 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :  159 (25225 expanded)
%              Number of leaves         :   45 (8954 expanded)
%              Depth                    :   24
%              Number of atoms          :  413 (74679 expanded)
%              Number of equality atoms :  105 (20120 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_186,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_164,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_76,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_83,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_76])).

tff(c_72,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_84,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_76])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1228,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_84,c_62])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1231,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1228,c_4])).

tff(c_1234,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1231])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_18,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1283,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_relset_1(A_143,B_144,C_145) = k2_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1287,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1228,c_1283])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1235,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_84,c_60])).

tff(c_1288,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_1235])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_85,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_64])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_85])).

tff(c_1297,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_94])).

tff(c_1295,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_1228])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1327,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1295,c_26])).

tff(c_1364,plain,(
    ! [B_157,A_158,C_159] :
      ( k1_xboole_0 = B_157
      | k1_relset_1(A_158,B_157,C_159) = A_158
      | ~ v1_funct_2(C_159,A_158,B_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1367,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1295,c_1364])).

tff(c_1370,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1327,c_1367])).

tff(c_1371,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1370])).

tff(c_1376,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1297])).

tff(c_1374,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1295])).

tff(c_1758,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( r2_funct_2(A_197,B_198,C_199,C_199)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_2(D_200,A_197,B_198)
      | ~ v1_funct_1(D_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_2(C_199,A_197,B_198)
      | ~ v1_funct_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1762,plain,(
    ! [C_199] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_199,C_199)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_199,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_199) ) ),
    inference(resolution,[status(thm)],[c_1374,c_1758])).

tff(c_1767,plain,(
    ! [C_201] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_201,C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_201,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_1762])).

tff(c_1772,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1767])).

tff(c_1776,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_1772])).

tff(c_24,plain,(
    ! [A_12] :
      ( k2_funct_1(k2_funct_1(A_12)) = A_12
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1293,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_1287])).

tff(c_1375,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1293])).

tff(c_1460,plain,(
    ! [C_169,A_170,B_171] :
      ( v1_funct_1(k2_funct_1(C_169))
      | k2_relset_1(A_170,B_171,C_169) != B_171
      | ~ v2_funct_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_2(C_169,A_170,B_171)
      | ~ v1_funct_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1463,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1460])).

tff(c_1466,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1463])).

tff(c_1467,plain,(
    ! [C_172,B_173,A_174] :
      ( v1_funct_2(k2_funct_1(C_172),B_173,A_174)
      | k2_relset_1(A_174,B_173,C_172) != B_173
      | ~ v2_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173)))
      | ~ v1_funct_2(C_172,A_174,B_173)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1470,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1467])).

tff(c_1473,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1470])).

tff(c_16,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1604,plain,(
    ! [C_182,B_183,A_184] :
      ( m1_subset_1(k2_funct_1(C_182),k1_zfmisc_1(k2_zfmisc_1(B_183,A_184)))
      | k2_relset_1(A_184,B_183,C_182) != B_183
      | ~ v2_funct_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183)))
      | ~ v1_funct_2(C_182,A_184,B_183)
      | ~ v1_funct_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1640,plain,(
    ! [C_182,B_183,A_184] :
      ( v1_relat_1(k2_funct_1(C_182))
      | ~ v1_relat_1(k2_zfmisc_1(B_183,A_184))
      | k2_relset_1(A_184,B_183,C_182) != B_183
      | ~ v2_funct_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183)))
      | ~ v1_funct_2(C_182,A_184,B_183)
      | ~ v1_funct_1(C_182) ) ),
    inference(resolution,[status(thm)],[c_1604,c_4])).

tff(c_1689,plain,(
    ! [C_187,A_188,B_189] :
      ( v1_relat_1(k2_funct_1(C_187))
      | k2_relset_1(A_188,B_189,C_187) != B_189
      | ~ v2_funct_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_2(C_187,A_188,B_189)
      | ~ v1_funct_1(C_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1640])).

tff(c_1695,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1689])).

tff(c_1699,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1695])).

tff(c_1715,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_relset_1(B_193,A_194,k2_funct_1(C_195)) = k1_relat_1(k2_funct_1(C_195))
      | k2_relset_1(A_194,B_193,C_195) != B_193
      | ~ v2_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193)))
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ v1_funct_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_1604,c_26])).

tff(c_1721,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1715])).

tff(c_1725,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1721])).

tff(c_40,plain,(
    ! [B_20,A_19,C_21] :
      ( k1_xboole_0 = B_20
      | k1_relset_1(A_19,B_20,C_21) = A_19
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1824,plain,(
    ! [A_208,B_209,C_210] :
      ( k1_xboole_0 = A_208
      | k1_relset_1(B_209,A_208,k2_funct_1(C_210)) = B_209
      | ~ v1_funct_2(k2_funct_1(C_210),B_209,A_208)
      | k2_relset_1(A_208,B_209,C_210) != B_209
      | ~ v2_funct_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ v1_funct_2(C_210,A_208,B_209)
      | ~ v1_funct_1(C_210) ) ),
    inference(resolution,[status(thm)],[c_1604,c_40])).

tff(c_1830,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1824])).

tff(c_1834,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1473,c_1725,c_1830])).

tff(c_1843,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1834])).

tff(c_10,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1430,plain,(
    ! [A_163,B_164] :
      ( v2_funct_1(A_163)
      | k2_relat_1(B_164) != k1_relat_1(A_163)
      | ~ v2_funct_1(k5_relat_1(B_164,A_163))
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1436,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k1_relat_1(k2_funct_1(A_11)) != k2_relat_1(A_11)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_11)))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1430])).

tff(c_1440,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k1_relat_1(k2_funct_1(A_11)) != k2_relat_1(A_11)
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1436])).

tff(c_1337,plain,(
    ! [A_149] :
      ( k5_relat_1(A_149,k2_funct_1(A_149)) = k6_relat_1(k1_relat_1(A_149))
      | ~ v2_funct_1(A_149)
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1346,plain,(
    ! [A_12] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_12))) = k5_relat_1(k2_funct_1(A_12),A_12)
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1337])).

tff(c_1851,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_1346])).

tff(c_1864,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_66,c_58,c_1699,c_1466,c_1851])).

tff(c_1883,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1864])).

tff(c_1889,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1440,c_1883])).

tff(c_1896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_66,c_58,c_1699,c_1466,c_1843,c_1889])).

tff(c_1898,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1864])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1700,plain,(
    ! [B_190,A_191,C_192] :
      ( k2_relset_1(B_190,A_191,k2_funct_1(C_192)) = k2_relat_1(k2_funct_1(C_192))
      | k2_relset_1(A_191,B_190,C_192) != B_190
      | ~ v2_funct_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190)))
      | ~ v1_funct_2(C_192,A_191,B_190)
      | ~ v1_funct_1(C_192) ) ),
    inference(resolution,[status(thm)],[c_1604,c_28])).

tff(c_1706,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1700])).

tff(c_1710,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1706])).

tff(c_48,plain,(
    ! [C_28,A_26,B_27] :
      ( v1_funct_1(k2_funct_1(C_28))
      | k2_relset_1(A_26,B_27,C_28) != B_27
      | ~ v2_funct_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1935,plain,(
    ! [C_215,B_216,A_217] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_215)))
      | k2_relset_1(B_216,A_217,k2_funct_1(C_215)) != A_217
      | ~ v2_funct_1(k2_funct_1(C_215))
      | ~ v1_funct_2(k2_funct_1(C_215),B_216,A_217)
      | ~ v1_funct_1(k2_funct_1(C_215))
      | k2_relset_1(A_217,B_216,C_215) != B_216
      | ~ v2_funct_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216)))
      | ~ v1_funct_2(C_215,A_217,B_216)
      | ~ v1_funct_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_1604,c_48])).

tff(c_1941,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1935])).

tff(c_1945,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1466,c_1473,c_1898,c_1710,c_1941])).

tff(c_1946,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1945])).

tff(c_1949,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1946])).

tff(c_1953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_66,c_58,c_1949])).

tff(c_1955,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1945])).

tff(c_1961,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1955,c_1710])).

tff(c_54,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_tops_2(A_31,B_32,C_33) = k2_funct_1(C_33)
      | ~ v2_funct_1(C_33)
      | k2_relset_1(A_31,B_32,C_33) != B_32
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2301,plain,(
    ! [B_231,A_232,C_233] :
      ( k2_tops_2(B_231,A_232,k2_funct_1(C_233)) = k2_funct_1(k2_funct_1(C_233))
      | ~ v2_funct_1(k2_funct_1(C_233))
      | k2_relset_1(B_231,A_232,k2_funct_1(C_233)) != A_232
      | ~ v1_funct_2(k2_funct_1(C_233),B_231,A_232)
      | ~ v1_funct_1(k2_funct_1(C_233))
      | k2_relset_1(A_232,B_231,C_233) != B_231
      | ~ v2_funct_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231)))
      | ~ v1_funct_2(C_233,A_232,B_231)
      | ~ v1_funct_1(C_233) ) ),
    inference(resolution,[status(thm)],[c_1604,c_54])).

tff(c_2307,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_2301])).

tff(c_2311,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_58,c_1375,c_1466,c_1473,c_1961,c_1898,c_2307])).

tff(c_1517,plain,(
    ! [A_176,B_177,C_178] :
      ( k2_tops_2(A_176,B_177,C_178) = k2_funct_1(C_178)
      | ~ v2_funct_1(C_178)
      | k2_relset_1(A_176,B_177,C_178) != B_177
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_2(C_178,A_176,B_177)
      | ~ v1_funct_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1520,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1374,c_1517])).

tff(c_1523,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1376,c_1375,c_58,c_1520])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1282,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_83,c_84,c_84,c_84,c_56])).

tff(c_1294,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_1288,c_1288,c_1282])).

tff(c_1373,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1371,c_1371,c_1294])).

tff(c_1524,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1373])).

tff(c_2312,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_1524])).

tff(c_2319,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2312])).

tff(c_2322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_66,c_58,c_1776,c_2319])).

tff(c_2324,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1834])).

tff(c_2360,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2324])).

tff(c_2364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_66,c_58,c_2360])).

tff(c_2365,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1370])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_95,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(u1_struct_0(A_43))
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_95])).

tff(c_105,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_101])).

tff(c_106,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_105])).

tff(c_1296,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_106])).

tff(c_2373,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2365,c_1296])).

tff(c_2377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:15:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/1.97  
% 5.12/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/1.97  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.12/1.97  
% 5.12/1.97  %Foreground sorts:
% 5.12/1.97  
% 5.12/1.97  
% 5.12/1.97  %Background operators:
% 5.12/1.97  
% 5.12/1.97  
% 5.12/1.97  %Foreground operators:
% 5.12/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.12/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.12/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.12/1.97  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.12/1.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.12/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.12/1.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.12/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.12/1.97  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.12/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.12/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.12/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.12/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.12/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.12/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.12/1.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.12/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.12/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.12/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.12/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.12/1.97  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.12/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.12/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.12/1.97  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.12/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.12/1.97  
% 5.47/1.99  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.47/1.99  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.47/1.99  tff(f_186, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 5.47/1.99  tff(f_144, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.47/1.99  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.47/1.99  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.47/1.99  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.47/1.99  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.47/1.99  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.47/1.99  tff(f_124, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 5.47/1.99  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.47/1.99  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.47/1.99  tff(f_39, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.47/1.99  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.47/1.99  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 5.47/1.99  tff(f_164, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.47/1.99  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.47/1.99  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.47/1.99  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.47/1.99  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_76, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.47/1.99  tff(c_83, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_76])).
% 5.47/1.99  tff(c_72, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_84, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_76])).
% 5.47/1.99  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_1228, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_84, c_62])).
% 5.47/1.99  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.47/1.99  tff(c_1231, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1228, c_4])).
% 5.47/1.99  tff(c_1234, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1231])).
% 5.47/1.99  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_18, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.47/1.99  tff(c_1283, plain, (![A_143, B_144, C_145]: (k2_relset_1(A_143, B_144, C_145)=k2_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.47/1.99  tff(c_1287, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1228, c_1283])).
% 5.47/1.99  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_1235, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_84, c_60])).
% 5.47/1.99  tff(c_1288, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1287, c_1235])).
% 5.47/1.99  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_85, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_64])).
% 5.47/1.99  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_85])).
% 5.47/1.99  tff(c_1297, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_94])).
% 5.47/1.99  tff(c_1295, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_1228])).
% 5.47/1.99  tff(c_26, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.47/1.99  tff(c_1327, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1295, c_26])).
% 5.47/1.99  tff(c_1364, plain, (![B_157, A_158, C_159]: (k1_xboole_0=B_157 | k1_relset_1(A_158, B_157, C_159)=A_158 | ~v1_funct_2(C_159, A_158, B_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.47/1.99  tff(c_1367, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1295, c_1364])).
% 5.47/1.99  tff(c_1370, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1327, c_1367])).
% 5.47/1.99  tff(c_1371, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1370])).
% 5.47/1.99  tff(c_1376, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1297])).
% 5.47/1.99  tff(c_1374, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1295])).
% 5.47/1.99  tff(c_1758, plain, (![A_197, B_198, C_199, D_200]: (r2_funct_2(A_197, B_198, C_199, C_199) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_2(D_200, A_197, B_198) | ~v1_funct_1(D_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_2(C_199, A_197, B_198) | ~v1_funct_1(C_199))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.47/1.99  tff(c_1762, plain, (![C_199]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_199, C_199) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_199, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_199))), inference(resolution, [status(thm)], [c_1374, c_1758])).
% 5.47/1.99  tff(c_1767, plain, (![C_201]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_201, C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_201, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_201))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_1762])).
% 5.47/1.99  tff(c_1772, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1767])).
% 5.47/1.99  tff(c_1776, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_1772])).
% 5.47/1.99  tff(c_24, plain, (![A_12]: (k2_funct_1(k2_funct_1(A_12))=A_12 | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.47/1.99  tff(c_1293, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_1287])).
% 5.47/1.99  tff(c_1375, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1293])).
% 5.47/1.99  tff(c_1460, plain, (![C_169, A_170, B_171]: (v1_funct_1(k2_funct_1(C_169)) | k2_relset_1(A_170, B_171, C_169)!=B_171 | ~v2_funct_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_2(C_169, A_170, B_171) | ~v1_funct_1(C_169))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.47/1.99  tff(c_1463, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1460])).
% 5.47/1.99  tff(c_1466, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1463])).
% 5.47/1.99  tff(c_1467, plain, (![C_172, B_173, A_174]: (v1_funct_2(k2_funct_1(C_172), B_173, A_174) | k2_relset_1(A_174, B_173, C_172)!=B_173 | ~v2_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))) | ~v1_funct_2(C_172, A_174, B_173) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.47/1.99  tff(c_1470, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1467])).
% 5.47/1.99  tff(c_1473, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1470])).
% 5.47/1.99  tff(c_16, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.47/1.99  tff(c_1604, plain, (![C_182, B_183, A_184]: (m1_subset_1(k2_funct_1(C_182), k1_zfmisc_1(k2_zfmisc_1(B_183, A_184))) | k2_relset_1(A_184, B_183, C_182)!=B_183 | ~v2_funct_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))) | ~v1_funct_2(C_182, A_184, B_183) | ~v1_funct_1(C_182))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.47/1.99  tff(c_1640, plain, (![C_182, B_183, A_184]: (v1_relat_1(k2_funct_1(C_182)) | ~v1_relat_1(k2_zfmisc_1(B_183, A_184)) | k2_relset_1(A_184, B_183, C_182)!=B_183 | ~v2_funct_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))) | ~v1_funct_2(C_182, A_184, B_183) | ~v1_funct_1(C_182))), inference(resolution, [status(thm)], [c_1604, c_4])).
% 5.47/1.99  tff(c_1689, plain, (![C_187, A_188, B_189]: (v1_relat_1(k2_funct_1(C_187)) | k2_relset_1(A_188, B_189, C_187)!=B_189 | ~v2_funct_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~v1_funct_2(C_187, A_188, B_189) | ~v1_funct_1(C_187))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1640])).
% 5.47/1.99  tff(c_1695, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1689])).
% 5.47/1.99  tff(c_1699, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1695])).
% 5.47/1.99  tff(c_1715, plain, (![B_193, A_194, C_195]: (k1_relset_1(B_193, A_194, k2_funct_1(C_195))=k1_relat_1(k2_funct_1(C_195)) | k2_relset_1(A_194, B_193, C_195)!=B_193 | ~v2_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))) | ~v1_funct_2(C_195, A_194, B_193) | ~v1_funct_1(C_195))), inference(resolution, [status(thm)], [c_1604, c_26])).
% 5.47/1.99  tff(c_1721, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1715])).
% 5.47/1.99  tff(c_1725, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1721])).
% 5.47/1.99  tff(c_40, plain, (![B_20, A_19, C_21]: (k1_xboole_0=B_20 | k1_relset_1(A_19, B_20, C_21)=A_19 | ~v1_funct_2(C_21, A_19, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.47/1.99  tff(c_1824, plain, (![A_208, B_209, C_210]: (k1_xboole_0=A_208 | k1_relset_1(B_209, A_208, k2_funct_1(C_210))=B_209 | ~v1_funct_2(k2_funct_1(C_210), B_209, A_208) | k2_relset_1(A_208, B_209, C_210)!=B_209 | ~v2_funct_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~v1_funct_2(C_210, A_208, B_209) | ~v1_funct_1(C_210))), inference(resolution, [status(thm)], [c_1604, c_40])).
% 5.47/1.99  tff(c_1830, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1824])).
% 5.47/1.99  tff(c_1834, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1473, c_1725, c_1830])).
% 5.47/1.99  tff(c_1843, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1834])).
% 5.47/1.99  tff(c_10, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.47/1.99  tff(c_22, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.47/1.99  tff(c_1430, plain, (![A_163, B_164]: (v2_funct_1(A_163) | k2_relat_1(B_164)!=k1_relat_1(A_163) | ~v2_funct_1(k5_relat_1(B_164, A_163)) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.47/1.99  tff(c_1436, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k1_relat_1(k2_funct_1(A_11))!=k2_relat_1(A_11) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_11))) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1430])).
% 5.47/1.99  tff(c_1440, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k1_relat_1(k2_funct_1(A_11))!=k2_relat_1(A_11) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1436])).
% 5.47/1.99  tff(c_1337, plain, (![A_149]: (k5_relat_1(A_149, k2_funct_1(A_149))=k6_relat_1(k1_relat_1(A_149)) | ~v2_funct_1(A_149) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.47/1.99  tff(c_1346, plain, (![A_12]: (k6_relat_1(k1_relat_1(k2_funct_1(A_12)))=k5_relat_1(k2_funct_1(A_12), A_12) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1337])).
% 5.47/1.99  tff(c_1851, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1843, c_1346])).
% 5.47/1.99  tff(c_1864, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_66, c_58, c_1699, c_1466, c_1851])).
% 5.47/1.99  tff(c_1883, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1864])).
% 5.47/1.99  tff(c_1889, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1440, c_1883])).
% 5.47/1.99  tff(c_1896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1234, c_66, c_58, c_1699, c_1466, c_1843, c_1889])).
% 5.47/1.99  tff(c_1898, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1864])).
% 5.47/1.99  tff(c_28, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.47/1.99  tff(c_1700, plain, (![B_190, A_191, C_192]: (k2_relset_1(B_190, A_191, k2_funct_1(C_192))=k2_relat_1(k2_funct_1(C_192)) | k2_relset_1(A_191, B_190, C_192)!=B_190 | ~v2_funct_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))) | ~v1_funct_2(C_192, A_191, B_190) | ~v1_funct_1(C_192))), inference(resolution, [status(thm)], [c_1604, c_28])).
% 5.47/1.99  tff(c_1706, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1700])).
% 5.47/1.99  tff(c_1710, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1706])).
% 5.47/1.99  tff(c_48, plain, (![C_28, A_26, B_27]: (v1_funct_1(k2_funct_1(C_28)) | k2_relset_1(A_26, B_27, C_28)!=B_27 | ~v2_funct_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.47/1.99  tff(c_1935, plain, (![C_215, B_216, A_217]: (v1_funct_1(k2_funct_1(k2_funct_1(C_215))) | k2_relset_1(B_216, A_217, k2_funct_1(C_215))!=A_217 | ~v2_funct_1(k2_funct_1(C_215)) | ~v1_funct_2(k2_funct_1(C_215), B_216, A_217) | ~v1_funct_1(k2_funct_1(C_215)) | k2_relset_1(A_217, B_216, C_215)!=B_216 | ~v2_funct_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))) | ~v1_funct_2(C_215, A_217, B_216) | ~v1_funct_1(C_215))), inference(resolution, [status(thm)], [c_1604, c_48])).
% 5.47/1.99  tff(c_1941, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1935])).
% 5.47/1.99  tff(c_1945, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1466, c_1473, c_1898, c_1710, c_1941])).
% 5.47/1.99  tff(c_1946, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1945])).
% 5.47/1.99  tff(c_1949, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1946])).
% 5.47/1.99  tff(c_1953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1234, c_66, c_58, c_1949])).
% 5.47/1.99  tff(c_1955, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1945])).
% 5.47/1.99  tff(c_1961, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1955, c_1710])).
% 5.47/1.99  tff(c_54, plain, (![A_31, B_32, C_33]: (k2_tops_2(A_31, B_32, C_33)=k2_funct_1(C_33) | ~v2_funct_1(C_33) | k2_relset_1(A_31, B_32, C_33)!=B_32 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.47/1.99  tff(c_2301, plain, (![B_231, A_232, C_233]: (k2_tops_2(B_231, A_232, k2_funct_1(C_233))=k2_funct_1(k2_funct_1(C_233)) | ~v2_funct_1(k2_funct_1(C_233)) | k2_relset_1(B_231, A_232, k2_funct_1(C_233))!=A_232 | ~v1_funct_2(k2_funct_1(C_233), B_231, A_232) | ~v1_funct_1(k2_funct_1(C_233)) | k2_relset_1(A_232, B_231, C_233)!=B_231 | ~v2_funct_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))) | ~v1_funct_2(C_233, A_232, B_231) | ~v1_funct_1(C_233))), inference(resolution, [status(thm)], [c_1604, c_54])).
% 5.47/1.99  tff(c_2307, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_2301])).
% 5.47/1.99  tff(c_2311, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_58, c_1375, c_1466, c_1473, c_1961, c_1898, c_2307])).
% 5.47/1.99  tff(c_1517, plain, (![A_176, B_177, C_178]: (k2_tops_2(A_176, B_177, C_178)=k2_funct_1(C_178) | ~v2_funct_1(C_178) | k2_relset_1(A_176, B_177, C_178)!=B_177 | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_2(C_178, A_176, B_177) | ~v1_funct_1(C_178))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.47/1.99  tff(c_1520, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1374, c_1517])).
% 5.47/1.99  tff(c_1523, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1376, c_1375, c_58, c_1520])).
% 5.47/1.99  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_1282, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_83, c_84, c_84, c_84, c_56])).
% 5.47/1.99  tff(c_1294, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_1288, c_1288, c_1282])).
% 5.47/1.99  tff(c_1373, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1371, c_1371, c_1294])).
% 5.47/1.99  tff(c_1524, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1373])).
% 5.47/1.99  tff(c_2312, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_1524])).
% 5.47/1.99  tff(c_2319, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2312])).
% 5.47/1.99  tff(c_2322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1234, c_66, c_58, c_1776, c_2319])).
% 5.47/1.99  tff(c_2324, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1834])).
% 5.47/1.99  tff(c_2360, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_2324])).
% 5.47/1.99  tff(c_2364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1234, c_66, c_58, c_2360])).
% 5.47/1.99  tff(c_2365, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1370])).
% 5.47/1.99  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.47/1.99  tff(c_95, plain, (![A_43]: (~v1_xboole_0(u1_struct_0(A_43)) | ~l1_struct_0(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.47/1.99  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83, c_95])).
% 5.47/1.99  tff(c_105, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_101])).
% 5.47/1.99  tff(c_106, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_105])).
% 5.47/1.99  tff(c_1296, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_106])).
% 5.47/1.99  tff(c_2373, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2365, c_1296])).
% 5.47/1.99  tff(c_2377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2373])).
% 5.47/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/1.99  
% 5.47/1.99  Inference rules
% 5.47/1.99  ----------------------
% 5.47/1.99  #Ref     : 0
% 5.47/1.99  #Sup     : 556
% 5.47/1.99  #Fact    : 0
% 5.47/1.99  #Define  : 0
% 5.47/2.00  #Split   : 9
% 5.47/2.00  #Chain   : 0
% 5.47/2.00  #Close   : 0
% 5.47/2.00  
% 5.47/2.00  Ordering : KBO
% 5.47/2.00  
% 5.47/2.00  Simplification rules
% 5.47/2.00  ----------------------
% 5.47/2.00  #Subsume      : 110
% 5.47/2.00  #Demod        : 637
% 5.47/2.00  #Tautology    : 301
% 5.47/2.00  #SimpNegUnit  : 3
% 5.47/2.00  #BackRed      : 84
% 5.47/2.00  
% 5.47/2.00  #Partial instantiations: 0
% 5.47/2.00  #Strategies tried      : 1
% 5.47/2.00  
% 5.47/2.00  Timing (in seconds)
% 5.47/2.00  ----------------------
% 5.47/2.00  Preprocessing        : 0.37
% 5.47/2.00  Parsing              : 0.19
% 5.47/2.00  CNF conversion       : 0.02
% 5.47/2.00  Main loop            : 0.85
% 5.47/2.00  Inferencing          : 0.30
% 5.47/2.00  Reduction            : 0.29
% 5.47/2.00  Demodulation         : 0.21
% 5.47/2.00  BG Simplification    : 0.04
% 5.47/2.00  Subsumption          : 0.17
% 5.47/2.00  Abstraction          : 0.04
% 5.47/2.00  MUC search           : 0.00
% 5.47/2.00  Cooper               : 0.00
% 5.47/2.00  Total                : 1.27
% 5.47/2.00  Index Insertion      : 0.00
% 5.47/2.00  Index Deletion       : 0.00
% 5.47/2.00  Index Matching       : 0.00
% 5.47/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
