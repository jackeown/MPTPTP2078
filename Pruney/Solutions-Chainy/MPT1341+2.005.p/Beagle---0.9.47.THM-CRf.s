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
% DateTime   : Thu Dec  3 10:23:46 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :  346 (81838 expanded)
%              Number of leaves         :   40 (29319 expanded)
%              Depth                    :   22
%              Number of atoms          :  912 (259243 expanded)
%              Number of equality atoms :  355 (105148 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(A),C,k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k6_partfun1(k1_relset_1(u1_struct_0(A),u1_struct_0(B),C))
                    & k1_partfun1(u1_struct_0(B),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),C) = k6_partfun1(k2_relset_1(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_2)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
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

tff(f_104,axiom,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_88,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_74,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_82,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_74])).

tff(c_58,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_81,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_74])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_52])).

tff(c_98,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_92,c_98])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_101])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_91,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_54])).

tff(c_123,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_127,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_123])).

tff(c_2339,plain,(
    ! [B_327,A_328,C_329] :
      ( k1_xboole_0 = B_327
      | k1_relset_1(A_328,B_327,C_329) = A_328
      | ~ v1_funct_2(C_329,A_328,B_327)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_328,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2342,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_2339])).

tff(c_2345,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_127,c_2342])).

tff(c_2346,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2345])).

tff(c_2351,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_91])).

tff(c_2350,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_92])).

tff(c_50,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_93,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_50])).

tff(c_2349,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_93])).

tff(c_2398,plain,(
    ! [C_333,A_334,B_335] :
      ( v1_funct_1(k2_funct_1(C_333))
      | k2_relset_1(A_334,B_335,C_333) != B_335
      | ~ v2_funct_1(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335)))
      | ~ v1_funct_2(C_333,A_334,B_335)
      | ~ v1_funct_1(C_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2401,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2350,c_2398])).

tff(c_2404,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2351,c_48,c_2349,c_2401])).

tff(c_2510,plain,(
    ! [B_357,C_358,A_359] :
      ( k6_partfun1(B_357) = k5_relat_1(k2_funct_1(C_358),C_358)
      | k1_xboole_0 = B_357
      | ~ v2_funct_1(C_358)
      | k2_relset_1(A_359,B_357,C_358) != B_357
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_357)))
      | ~ v1_funct_2(C_358,A_359,B_357)
      | ~ v1_funct_1(C_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2514,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2350,c_2510])).

tff(c_2518,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2351,c_2349,c_48,c_2514])).

tff(c_2519,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2518])).

tff(c_2529,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_2351])).

tff(c_2527,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_2350])).

tff(c_18,plain,(
    ! [C_13,A_11] :
      ( k1_xboole_0 = C_13
      | ~ v1_funct_2(C_13,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2575,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0)
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2527,c_18])).

tff(c_2611,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2529,c_2575])).

tff(c_2627,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2611])).

tff(c_2633,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2529])).

tff(c_2528,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_2519,c_2349])).

tff(c_2632,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2528])).

tff(c_2405,plain,(
    ! [C_336,B_337,A_338] :
      ( v1_funct_2(k2_funct_1(C_336),B_337,A_338)
      | k2_relset_1(A_338,B_337,C_336) != B_337
      | ~ v2_funct_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337)))
      | ~ v1_funct_2(C_336,A_338,B_337)
      | ~ v1_funct_1(C_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2408,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2350,c_2405])).

tff(c_2411,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2351,c_48,c_2349,c_2408])).

tff(c_2525,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_2411])).

tff(c_2631,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2525])).

tff(c_2628,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2527])).

tff(c_2446,plain,(
    ! [C_351,B_352,A_353] :
      ( m1_subset_1(k2_funct_1(C_351),k1_zfmisc_1(k2_zfmisc_1(B_352,A_353)))
      | k2_relset_1(A_353,B_352,C_351) != B_352
      | ~ v2_funct_1(C_351)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_353,B_352)))
      | ~ v1_funct_2(C_351,A_353,B_352)
      | ~ v1_funct_1(C_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2495,plain,(
    ! [B_352,A_353,C_351] :
      ( k1_relset_1(B_352,A_353,k2_funct_1(C_351)) = k1_relat_1(k2_funct_1(C_351))
      | k2_relset_1(A_353,B_352,C_351) != B_352
      | ~ v2_funct_1(C_351)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_353,B_352)))
      | ~ v1_funct_2(C_351,A_353,B_352)
      | ~ v1_funct_1(C_351) ) ),
    inference(resolution,[status(thm)],[c_2446,c_14])).

tff(c_2667,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2628,c_2495])).

tff(c_2709,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2633,c_48,c_2632,c_2667])).

tff(c_24,plain,(
    ! [B_12,C_13] :
      ( k1_relset_1(k1_xboole_0,B_12,C_13) = k1_xboole_0
      | ~ v1_funct_2(C_13,k1_xboole_0,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2797,plain,(
    ! [A_371,C_372] :
      ( k1_relset_1(k1_xboole_0,A_371,k2_funct_1(C_372)) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_372),k1_xboole_0,A_371)
      | k2_relset_1(A_371,k1_xboole_0,C_372) != k1_xboole_0
      | ~ v2_funct_1(C_372)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_371,k1_xboole_0)))
      | ~ v1_funct_2(C_372,A_371,k1_xboole_0)
      | ~ v1_funct_1(C_372) ) ),
    inference(resolution,[status(thm)],[c_2446,c_24])).

tff(c_2800,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0)
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2628,c_2797])).

tff(c_2807,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2633,c_48,c_2632,c_2631,c_2709,c_2800])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2813,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2807,c_8])).

tff(c_2820,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_2813])).

tff(c_30,plain,(
    ! [A_20] : k6_relat_1(A_20) = k6_partfun1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_2429,plain,(
    ! [C_345,B_346,E_342,A_347,F_343,D_344] :
      ( k1_partfun1(A_347,B_346,C_345,D_344,E_342,F_343) = k5_relat_1(E_342,F_343)
      | ~ m1_subset_1(F_343,k1_zfmisc_1(k2_zfmisc_1(C_345,D_344)))
      | ~ v1_funct_1(F_343)
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(A_347,B_346)))
      | ~ v1_funct_1(E_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2431,plain,(
    ! [A_347,B_346,E_342] :
      ( k1_partfun1(A_347,B_346,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),E_342,'#skF_3') = k5_relat_1(E_342,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(A_347,B_346)))
      | ~ v1_funct_1(E_342) ) ),
    inference(resolution,[status(thm)],[c_2350,c_2429])).

tff(c_2434,plain,(
    ! [A_347,B_346,E_342] :
      ( k1_partfun1(A_347,B_346,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),E_342,'#skF_3') = k5_relat_1(E_342,'#skF_3')
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(A_347,B_346)))
      | ~ v1_funct_1(E_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2431])).

tff(c_2485,plain,(
    ! [B_352,A_353,C_351] :
      ( k1_partfun1(B_352,A_353,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_funct_1(C_351),'#skF_3') = k5_relat_1(k2_funct_1(C_351),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_351))
      | k2_relset_1(A_353,B_352,C_351) != B_352
      | ~ v2_funct_1(C_351)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_353,B_352)))
      | ~ v1_funct_2(C_351,A_353,B_352)
      | ~ v1_funct_1(C_351) ) ),
    inference(resolution,[status(thm)],[c_2446,c_2434])).

tff(c_2830,plain,(
    ! [B_373,A_374,C_375] :
      ( k1_partfun1(B_373,A_374,k1_xboole_0,k1_xboole_0,k2_funct_1(C_375),'#skF_3') = k5_relat_1(k2_funct_1(C_375),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_375))
      | k2_relset_1(A_374,B_373,C_375) != B_373
      | ~ v2_funct_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_374,B_373)))
      | ~ v1_funct_2(C_375,A_374,B_373)
      | ~ v1_funct_1(C_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2519,c_2485])).

tff(c_2833,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2628,c_2830])).

tff(c_2839,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2633,c_48,c_2632,c_2404,c_2833])).

tff(c_2412,plain,(
    ! [A_339,B_340,C_341] :
      ( k2_tops_2(A_339,B_340,C_341) = k2_funct_1(C_341)
      | ~ v2_funct_1(C_341)
      | k2_relset_1(A_339,B_340,C_341) != B_340
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ v1_funct_2(C_341,A_339,B_340)
      | ~ v1_funct_1(C_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2415,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2350,c_2412])).

tff(c_2418,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2351,c_2349,c_48,c_2415])).

tff(c_12,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_156,plain,(
    ! [B_55,A_56,C_57] :
      ( k1_xboole_0 = B_55
      | k1_relset_1(A_56,B_55,C_57) = A_56
      | ~ v1_funct_2(C_57,A_56,B_55)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_159,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_156])).

tff(c_162,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_127,c_159])).

tff(c_163,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_167,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_91])).

tff(c_165,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_93])).

tff(c_166,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_92])).

tff(c_317,plain,(
    ! [B_85,C_86,A_87] :
      ( k6_partfun1(B_85) = k5_relat_1(k2_funct_1(C_86),C_86)
      | k1_xboole_0 = B_85
      | ~ v2_funct_1(C_86)
      | k2_relset_1(A_87,B_85,C_86) != B_85
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_85)))
      | ~ v1_funct_2(C_86,A_87,B_85)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_321,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_166,c_317])).

tff(c_325,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167,c_165,c_48,c_321])).

tff(c_326,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_335,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_167])).

tff(c_333,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_166])).

tff(c_387,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0)
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_333,c_18])).

tff(c_427,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_387])).

tff(c_433,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_439,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_335])).

tff(c_332,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_165])).

tff(c_437,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_332])).

tff(c_210,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_funct_1(k2_funct_1(C_61))
      | k2_relset_1(A_62,B_63,C_61) != B_63
      | ~ v2_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_2(C_61,A_62,B_63)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_213,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_166,c_210])).

tff(c_216,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167,c_48,c_165,c_213])).

tff(c_434,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_333])).

tff(c_253,plain,(
    ! [C_79,B_80,A_81] :
      ( m1_subset_1(k2_funct_1(C_79),k1_zfmisc_1(k2_zfmisc_1(B_80,A_81)))
      | k2_relset_1(A_81,B_80,C_79) != B_80
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_2(C_79,A_81,B_80)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] :
      ( k1_partfun1(A_14,B_15,C_16,D_17,E_18,F_19) = k5_relat_1(E_18,F_19)
      | ~ m1_subset_1(F_19,k1_zfmisc_1(k2_zfmisc_1(C_16,D_17)))
      | ~ v1_funct_1(F_19)
      | ~ m1_subset_1(E_18,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_1(E_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_686,plain,(
    ! [B_115,A_118,B_116,C_117,E_113,A_114] :
      ( k1_partfun1(A_118,B_116,B_115,A_114,E_113,k2_funct_1(C_117)) = k5_relat_1(E_113,k2_funct_1(C_117))
      | ~ v1_funct_1(k2_funct_1(C_117))
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_118,B_116)))
      | ~ v1_funct_1(E_113)
      | k2_relset_1(A_114,B_115,C_117) != B_115
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_2(C_117,A_114,B_115)
      | ~ v1_funct_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_253,c_28])).

tff(c_688,plain,(
    ! [B_115,A_114,C_117] :
      ( k1_partfun1(k1_xboole_0,k1_xboole_0,B_115,A_114,'#skF_3',k2_funct_1(C_117)) = k5_relat_1('#skF_3',k2_funct_1(C_117))
      | ~ v1_funct_1(k2_funct_1(C_117))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_114,B_115,C_117) != B_115
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_2(C_117,A_114,B_115)
      | ~ v1_funct_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_434,c_686])).

tff(c_695,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_partfun1(k1_xboole_0,k1_xboole_0,B_119,A_120,'#skF_3',k2_funct_1(C_121)) = k5_relat_1('#skF_3',k2_funct_1(C_121))
      | ~ v1_funct_1(k2_funct_1(C_121))
      | k2_relset_1(A_120,B_119,C_121) != B_119
      | ~ v2_funct_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ v1_funct_1(C_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_688])).

tff(c_698,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_434,c_695])).

tff(c_704,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_439,c_48,c_437,c_216,c_698])).

tff(c_224,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_tops_2(A_67,B_68,C_69) = k2_funct_1(C_69)
      | ~ v2_funct_1(C_69)
      | k2_relset_1(A_67,B_68,C_69) != B_68
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(C_69,A_67,B_68)
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_227,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_166,c_224])).

tff(c_230,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167,c_165,c_48,c_227])).

tff(c_46,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_61,plain,
    ( k1_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_3',k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46])).

tff(c_133,plain,
    ( k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2'))
    | k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_82,c_82,c_82,c_82,c_81,c_81,c_81,c_81,c_82,c_82,c_82,c_81,c_81,c_81,c_61])).

tff(c_134,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_209,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),'#skF_3',k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_163,c_163,c_134])).

tff(c_231,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_209])).

tff(c_329,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k1_xboole_0,k1_xboole_0,k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_231])).

tff(c_572,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_433,c_433,c_329])).

tff(c_706,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_572])).

tff(c_713,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1(k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_706])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_433,c_713])).

tff(c_717,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_736,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_335])).

tff(c_734,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_717,c_332])).

tff(c_730,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_333])).

tff(c_1003,plain,(
    ! [B_163,A_165,A_161,C_164,B_162,E_160] :
      ( k1_partfun1(A_165,B_163,B_162,A_161,E_160,k2_funct_1(C_164)) = k5_relat_1(E_160,k2_funct_1(C_164))
      | ~ v1_funct_1(k2_funct_1(C_164))
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_165,B_163)))
      | ~ v1_funct_1(E_160)
      | k2_relset_1(A_161,B_162,C_164) != B_162
      | ~ v2_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_2(C_164,A_161,B_162)
      | ~ v1_funct_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_253,c_28])).

tff(c_1005,plain,(
    ! [B_162,A_161,C_164] :
      ( k1_partfun1(k1_relat_1('#skF_3'),'#skF_3',B_162,A_161,'#skF_3',k2_funct_1(C_164)) = k5_relat_1('#skF_3',k2_funct_1(C_164))
      | ~ v1_funct_1(k2_funct_1(C_164))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_161,B_162,C_164) != B_162
      | ~ v2_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_2(C_164,A_161,B_162)
      | ~ v1_funct_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_730,c_1003])).

tff(c_1013,plain,(
    ! [B_166,A_167,C_168] :
      ( k1_partfun1(k1_relat_1('#skF_3'),'#skF_3',B_166,A_167,'#skF_3',k2_funct_1(C_168)) = k5_relat_1('#skF_3',k2_funct_1(C_168))
      | ~ v1_funct_1(k2_funct_1(C_168))
      | k2_relset_1(A_167,B_166,C_168) != B_166
      | ~ v2_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166)))
      | ~ v1_funct_2(C_168,A_167,B_166)
      | ~ v1_funct_1(C_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1005])).

tff(c_1016,plain,
    ( k1_partfun1(k1_relat_1('#skF_3'),'#skF_3','#skF_3',k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_730,c_1013])).

tff(c_1022,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),'#skF_3','#skF_3',k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_736,c_48,c_734,c_216,c_1016])).

tff(c_842,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),'#skF_3','#skF_3',k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_717,c_329])).

tff(c_1024,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_842])).

tff(c_1031,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1024])).

tff(c_1035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_1031])).

tff(c_1037,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_217,plain,(
    ! [C_64,B_65,A_66] :
      ( v1_funct_2(k2_funct_1(C_64),B_65,A_66)
      | k2_relset_1(A_66,B_65,C_64) != B_65
      | ~ v2_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65)))
      | ~ v1_funct_2(C_64,A_66,B_65)
      | ~ v1_funct_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_220,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_166,c_217])).

tff(c_223,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167,c_48,c_165,c_220])).

tff(c_1100,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_relset_1(B_172,A_173,k2_funct_1(C_174)) = k1_relat_1(k2_funct_1(C_174))
      | k2_relset_1(A_173,B_172,C_174) != B_172
      | ~ v2_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172)))
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ v1_funct_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_253,c_14])).

tff(c_1106,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_166,c_1100])).

tff(c_1110,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167,c_48,c_165,c_1106])).

tff(c_26,plain,(
    ! [B_12,A_11,C_13] :
      ( k1_xboole_0 = B_12
      | k1_relset_1(A_11,B_12,C_13) = A_11
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1127,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_xboole_0 = A_179
      | k1_relset_1(B_180,A_179,k2_funct_1(C_181)) = B_180
      | ~ v1_funct_2(k2_funct_1(C_181),B_180,A_179)
      | k2_relset_1(A_179,B_180,C_181) != B_180
      | ~ v2_funct_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(C_181,A_179,B_180)
      | ~ v1_funct_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_253,c_26])).

tff(c_1133,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_166,c_1127])).

tff(c_1137,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167,c_48,c_165,c_223,c_1110,c_1133])).

tff(c_1138,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1137])).

tff(c_1143,plain,
    ( k2_struct_0('#skF_2') = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_8])).

tff(c_1150,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_1143])).

tff(c_1176,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_167])).

tff(c_1174,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_166])).

tff(c_1173,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1150,c_165])).

tff(c_1058,plain,(
    ! [A_169,C_170,B_171] :
      ( k6_partfun1(A_169) = k5_relat_1(C_170,k2_funct_1(C_170))
      | k1_xboole_0 = B_171
      | ~ v2_funct_1(C_170)
      | k2_relset_1(A_169,B_171,C_170) != B_171
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_171)))
      | ~ v1_funct_2(C_170,A_169,B_171)
      | ~ v1_funct_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1062,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_struct_0('#skF_2') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_166,c_1058])).

tff(c_1066,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167,c_165,c_48,c_1062])).

tff(c_1067,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1037,c_1066])).

tff(c_1311,plain,(
    ! [E_188,B_191,A_193,B_190,A_189,C_192] :
      ( k1_partfun1(A_193,B_191,B_190,A_189,E_188,k2_funct_1(C_192)) = k5_relat_1(E_188,k2_funct_1(C_192))
      | ~ v1_funct_1(k2_funct_1(C_192))
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_193,B_191)))
      | ~ v1_funct_1(E_188)
      | k2_relset_1(A_189,B_190,C_192) != B_190
      | ~ v2_funct_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_2(C_192,A_189,B_190)
      | ~ v1_funct_1(C_192) ) ),
    inference(resolution,[status(thm)],[c_253,c_28])).

tff(c_1313,plain,(
    ! [B_190,A_189,C_192] :
      ( k1_partfun1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),B_190,A_189,'#skF_3',k2_funct_1(C_192)) = k5_relat_1('#skF_3',k2_funct_1(C_192))
      | ~ v1_funct_1(k2_funct_1(C_192))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_189,B_190,C_192) != B_190
      | ~ v2_funct_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_2(C_192,A_189,B_190)
      | ~ v1_funct_1(C_192) ) ),
    inference(resolution,[status(thm)],[c_1174,c_1311])).

tff(c_1347,plain,(
    ! [B_200,A_201,C_202] :
      ( k1_partfun1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),B_200,A_201,'#skF_3',k2_funct_1(C_202)) = k5_relat_1('#skF_3',k2_funct_1(C_202))
      | ~ v1_funct_1(k2_funct_1(C_202))
      | k2_relset_1(A_201,B_200,C_202) != B_200
      | ~ v2_funct_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200)))
      | ~ v1_funct_2(C_202,A_201,B_200)
      | ~ v1_funct_1(C_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1313])).

tff(c_1170,plain,(
    k1_partfun1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1150,c_231])).

tff(c_1353,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_1170])).

tff(c_1360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1176,c_1174,c_48,c_1173,c_216,c_1067,c_1353])).

tff(c_1361,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1137])).

tff(c_1373,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_167])).

tff(c_1370,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_165])).

tff(c_1369,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_223])).

tff(c_1371,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_166])).

tff(c_301,plain,(
    ! [C_79,B_80] :
      ( k2_funct_1(C_79) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_79),B_80,k1_xboole_0)
      | k1_xboole_0 = B_80
      | k2_relset_1(k1_xboole_0,B_80,C_79) != B_80
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_80)))
      | ~ v1_funct_2(C_79,k1_xboole_0,B_80)
      | ~ v1_funct_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_253,c_18])).

tff(c_1428,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_xboole_0)
    | k2_struct_0('#skF_2') = k1_xboole_0
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1371,c_301])).

tff(c_1477,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1373,c_48,c_1370,c_1369,c_1428])).

tff(c_1478,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1037,c_1477])).

tff(c_1367,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_1361,c_1361,c_231])).

tff(c_1612,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k1_xboole_0) != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1367])).

tff(c_1538,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_216])).

tff(c_1364,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_1067])).

tff(c_1533,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1364])).

tff(c_1524,plain,(
    ! [A_207,B_208,E_206,B_209,C_210,A_211] :
      ( k1_partfun1(A_211,B_209,B_208,A_207,E_206,k2_funct_1(C_210)) = k5_relat_1(E_206,k2_funct_1(C_210))
      | ~ v1_funct_1(k2_funct_1(C_210))
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_211,B_209)))
      | ~ v1_funct_1(E_206)
      | k2_relset_1(A_207,B_208,C_210) != B_208
      | ~ v2_funct_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(C_210,A_207,B_208)
      | ~ v1_funct_1(C_210) ) ),
    inference(resolution,[status(thm)],[c_253,c_28])).

tff(c_1526,plain,(
    ! [B_208,A_207,C_210] :
      ( k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),B_208,A_207,'#skF_3',k2_funct_1(C_210)) = k5_relat_1('#skF_3',k2_funct_1(C_210))
      | ~ v1_funct_1(k2_funct_1(C_210))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_207,B_208,C_210) != B_208
      | ~ v2_funct_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(C_210,A_207,B_208)
      | ~ v1_funct_1(C_210) ) ),
    inference(resolution,[status(thm)],[c_1371,c_1524])).

tff(c_1811,plain,(
    ! [B_233,A_234,C_235] :
      ( k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),B_233,A_234,'#skF_3',k2_funct_1(C_235)) = k5_relat_1('#skF_3',k2_funct_1(C_235))
      | ~ v1_funct_1(k2_funct_1(C_235))
      | k2_relset_1(A_234,B_233,C_235) != B_233
      | ~ v2_funct_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_234,B_233)))
      | ~ v1_funct_2(C_235,A_234,B_233)
      | ~ v1_funct_1(C_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1526])).

tff(c_1817,plain,
    ( k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1371,c_1811])).

tff(c_1826,plain,(
    k1_partfun1(k1_xboole_0,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k1_xboole_0,'#skF_3',k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1373,c_48,c_1370,c_1538,c_1478,c_1533,c_1478,c_1478,c_1817])).

tff(c_1828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1612,c_1826])).

tff(c_1829,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_1834,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_91])).

tff(c_1833,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_92])).

tff(c_1861,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1833,c_18])).

tff(c_1877,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_1861])).

tff(c_1883,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1877])).

tff(c_1830,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_1890,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1830])).

tff(c_1889,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1834])).

tff(c_1886,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1833])).

tff(c_1916,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1886,c_24])).

tff(c_1941,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_1916])).

tff(c_1831,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_127])).

tff(c_1887,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1831])).

tff(c_1956,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1941,c_1887])).

tff(c_1957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1890,c_1956])).

tff(c_1958,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1877])).

tff(c_1964,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1958,c_1834])).

tff(c_1832,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_1829,c_93])).

tff(c_1963,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1958,c_1958,c_1832])).

tff(c_1960,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1958,c_1833])).

tff(c_36,plain,(
    ! [C_23,A_21,B_22] :
      ( v1_funct_1(k2_funct_1(C_23))
      | k2_relset_1(A_21,B_22,C_23) != B_22
      | ~ v2_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1992,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1960,c_36])).

tff(c_2001,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1964,c_48,c_1963,c_1992])).

tff(c_2077,plain,(
    ! [C_273,B_274,A_275] :
      ( m1_subset_1(k2_funct_1(C_273),k1_zfmisc_1(k2_zfmisc_1(B_274,A_275)))
      | k2_relset_1(A_275,B_274,C_273) != B_274
      | ~ v2_funct_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_275,B_274)))
      | ~ v1_funct_2(C_273,A_275,B_274)
      | ~ v1_funct_1(C_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2284,plain,(
    ! [C_312,A_315,A_314,B_311,E_310,B_313] :
      ( k1_partfun1(A_314,B_313,B_311,A_315,E_310,k2_funct_1(C_312)) = k5_relat_1(E_310,k2_funct_1(C_312))
      | ~ v1_funct_1(k2_funct_1(C_312))
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(A_314,B_313)))
      | ~ v1_funct_1(E_310)
      | k2_relset_1(A_315,B_311,C_312) != B_311
      | ~ v2_funct_1(C_312)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_315,B_311)))
      | ~ v1_funct_2(C_312,A_315,B_311)
      | ~ v1_funct_1(C_312) ) ),
    inference(resolution,[status(thm)],[c_2077,c_28])).

tff(c_2288,plain,(
    ! [B_311,A_315,C_312] :
      ( k1_partfun1(k2_struct_0('#skF_1'),'#skF_3',B_311,A_315,'#skF_3',k2_funct_1(C_312)) = k5_relat_1('#skF_3',k2_funct_1(C_312))
      | ~ v1_funct_1(k2_funct_1(C_312))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_315,B_311,C_312) != B_311
      | ~ v2_funct_1(C_312)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_315,B_311)))
      | ~ v1_funct_2(C_312,A_315,B_311)
      | ~ v1_funct_1(C_312) ) ),
    inference(resolution,[status(thm)],[c_1960,c_2284])).

tff(c_2293,plain,(
    ! [B_316,A_317,C_318] :
      ( k1_partfun1(k2_struct_0('#skF_1'),'#skF_3',B_316,A_317,'#skF_3',k2_funct_1(C_318)) = k5_relat_1('#skF_3',k2_funct_1(C_318))
      | ~ v1_funct_1(k2_funct_1(C_318))
      | k2_relset_1(A_317,B_316,C_318) != B_316
      | ~ v2_funct_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_317,B_316)))
      | ~ v1_funct_2(C_318,A_317,B_316)
      | ~ v1_funct_1(C_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2288])).

tff(c_2299,plain,
    ( k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1960,c_2293])).

tff(c_2303,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1964,c_48,c_1963,c_2001,c_2299])).

tff(c_2043,plain,(
    ! [A_258,B_259,C_260] :
      ( k2_tops_2(A_258,B_259,C_260) = k2_funct_1(C_260)
      | ~ v2_funct_1(C_260)
      | k2_relset_1(A_258,B_259,C_260) != B_259
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_260,A_258,B_259)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2046,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1960,c_2043])).

tff(c_2049,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1964,c_1963,c_48,c_2046])).

tff(c_1966,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1958,c_1829])).

tff(c_2006,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_1966,c_1966,c_134])).

tff(c_2050,plain,(
    k1_partfun1(k2_struct_0('#skF_1'),'#skF_3','#skF_3',k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_2006])).

tff(c_2304,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2303,c_2050])).

tff(c_2311,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2304])).

tff(c_2315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_2311])).

tff(c_2316,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2347,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_2346,c_2346,c_2316])).

tff(c_2419,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2347])).

tff(c_2523,plain,(
    k1_partfun1(k1_xboole_0,k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_2519,c_2519,c_2419])).

tff(c_2760,plain,(
    k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2627,c_2523])).

tff(c_2845,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_2760])).

tff(c_2852,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1(k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_2845])).

tff(c_2855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_2820,c_2852])).

tff(c_2856,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2611])).

tff(c_2864,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2529])).

tff(c_2863,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2856,c_2528])).

tff(c_2862,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2525])).

tff(c_2859,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2527])).

tff(c_2902,plain,
    ( k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2859,c_2495])).

tff(c_2925,plain,(
    k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2864,c_48,c_2863,c_2902])).

tff(c_2492,plain,(
    ! [A_353,C_351] :
      ( k1_relset_1(k1_xboole_0,A_353,k2_funct_1(C_351)) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_351),k1_xboole_0,A_353)
      | k2_relset_1(A_353,k1_xboole_0,C_351) != k1_xboole_0
      | ~ v2_funct_1(C_351)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_353,k1_xboole_0)))
      | ~ v1_funct_2(C_351,A_353,k1_xboole_0)
      | ~ v1_funct_1(C_351) ) ),
    inference(resolution,[status(thm)],[c_2446,c_24])).

tff(c_3019,plain,(
    ! [A_391,C_392] :
      ( k1_relset_1('#skF_3',A_391,k2_funct_1(C_392)) = '#skF_3'
      | ~ v1_funct_2(k2_funct_1(C_392),'#skF_3',A_391)
      | k2_relset_1(A_391,'#skF_3',C_392) != '#skF_3'
      | ~ v2_funct_1(C_392)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_391,'#skF_3')))
      | ~ v1_funct_2(C_392,A_391,'#skF_3')
      | ~ v1_funct_1(C_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2856,c_2856,c_2856,c_2856,c_2856,c_2856,c_2492])).

tff(c_3022,plain,
    ( k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2859,c_3019])).

tff(c_3029,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2864,c_48,c_2863,c_2862,c_2925,c_3022])).

tff(c_3035,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3029,c_8])).

tff(c_3042,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_3035])).

tff(c_2866,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2519])).

tff(c_3114,plain,(
    ! [B_408,A_409,C_410] :
      ( k1_partfun1(B_408,A_409,k1_relat_1('#skF_3'),'#skF_3',k2_funct_1(C_410),'#skF_3') = k5_relat_1(k2_funct_1(C_410),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_410))
      | k2_relset_1(A_409,B_408,C_410) != B_408
      | ~ v2_funct_1(C_410)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408)))
      | ~ v1_funct_2(C_410,A_409,B_408)
      | ~ v1_funct_1(C_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2866,c_2485])).

tff(c_3117,plain,
    ( k1_partfun1('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2859,c_3114])).

tff(c_3123,plain,(
    k1_partfun1('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2864,c_48,c_2863,c_2404,c_3117])).

tff(c_2962,plain,(
    k1_partfun1('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2856,c_2856,c_2523])).

tff(c_3125,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3123,c_2962])).

tff(c_3132,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3125])).

tff(c_3135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_3042,c_3132])).

tff(c_3136,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2518])).

tff(c_3141,plain,
    ( k6_partfun1(k2_struct_0('#skF_2')) = k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3136,c_63])).

tff(c_3148,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_3141])).

tff(c_3152,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3148,c_3136])).

tff(c_3153,plain,(
    k1_partfun1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3148,c_2419])).

tff(c_3212,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2485,c_3153])).

tff(c_3215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2351,c_2350,c_48,c_2349,c_2404,c_3152,c_3212])).

tff(c_3216,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2345])).

tff(c_3221,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_91])).

tff(c_3220,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_92])).

tff(c_3244,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3220,c_18])).

tff(c_3260,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3221,c_3244])).

tff(c_3265,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3260])).

tff(c_3217,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2345])).

tff(c_3274,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_3217])).

tff(c_3273,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_3221])).

tff(c_3271,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_3220])).

tff(c_3300,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3271,c_24])).

tff(c_3325,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3273,c_3300])).

tff(c_3261,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3220,c_14])).

tff(c_3340,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3325,c_3265,c_3261])).

tff(c_3341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3274,c_3340])).

tff(c_3342,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3260])).

tff(c_3347,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_3221])).

tff(c_3219,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_3216,c_93])).

tff(c_3345,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_3342,c_3219])).

tff(c_3344,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_3220])).

tff(c_3414,plain,(
    ! [C_433,B_434,A_435] :
      ( v1_funct_2(k2_funct_1(C_433),B_434,A_435)
      | k2_relset_1(A_435,B_434,C_433) != B_434
      | ~ v2_funct_1(C_433)
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(A_435,B_434)))
      | ~ v1_funct_2(C_433,A_435,B_434)
      | ~ v1_funct_1(C_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3417,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3344,c_3414])).

tff(c_3420,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3347,c_48,c_3345,c_3417])).

tff(c_3459,plain,(
    ! [C_445,B_446,A_447] :
      ( m1_subset_1(k2_funct_1(C_445),k1_zfmisc_1(k2_zfmisc_1(B_446,A_447)))
      | k2_relset_1(A_447,B_446,C_445) != B_446
      | ~ v2_funct_1(C_445)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_447,B_446)))
      | ~ v1_funct_2(C_445,A_447,B_446)
      | ~ v1_funct_1(C_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3562,plain,(
    ! [B_466,A_467,C_468] :
      ( k1_relset_1(B_466,A_467,k2_funct_1(C_468)) = k1_relat_1(k2_funct_1(C_468))
      | k2_relset_1(A_467,B_466,C_468) != B_466
      | ~ v2_funct_1(C_468)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_467,B_466)))
      | ~ v1_funct_2(C_468,A_467,B_466)
      | ~ v1_funct_1(C_468) ) ),
    inference(resolution,[status(thm)],[c_3459,c_14])).

tff(c_3568,plain,
    ( k1_relset_1('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3344,c_3562])).

tff(c_3572,plain,(
    k1_relset_1('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3347,c_48,c_3345,c_3568])).

tff(c_3351,plain,(
    ! [B_12,C_13] :
      ( k1_relset_1('#skF_3',B_12,C_13) = '#skF_3'
      | ~ v1_funct_2(C_13,'#skF_3',B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_12))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_3342,c_3342,c_3342,c_24])).

tff(c_3616,plain,(
    ! [A_477,C_478] :
      ( k1_relset_1('#skF_3',A_477,k2_funct_1(C_478)) = '#skF_3'
      | ~ v1_funct_2(k2_funct_1(C_478),'#skF_3',A_477)
      | k2_relset_1(A_477,'#skF_3',C_478) != '#skF_3'
      | ~ v2_funct_1(C_478)
      | ~ m1_subset_1(C_478,k1_zfmisc_1(k2_zfmisc_1(A_477,'#skF_3')))
      | ~ v1_funct_2(C_478,A_477,'#skF_3')
      | ~ v1_funct_1(C_478) ) ),
    inference(resolution,[status(thm)],[c_3459,c_3351])).

tff(c_3623,plain,
    ( k1_relset_1('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3344,c_3616])).

tff(c_3627,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3347,c_48,c_3345,c_3420,c_3572,c_3623])).

tff(c_3632,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3627,c_8])).

tff(c_3639,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_3632])).

tff(c_3380,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3344,c_36])).

tff(c_3389,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3347,c_48,c_3345,c_3380])).

tff(c_32,plain,(
    ! [C_23,B_22,A_21] :
      ( m1_subset_1(k2_funct_1(C_23),k1_zfmisc_1(k2_zfmisc_1(B_22,A_21)))
      | k2_relset_1(A_21,B_22,C_23) != B_22
      | ~ v2_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3516,plain,(
    ! [C_454,F_452,B_455,A_456,E_451,D_453] :
      ( k1_partfun1(A_456,B_455,C_454,D_453,E_451,F_452) = k5_relat_1(E_451,F_452)
      | ~ m1_subset_1(F_452,k1_zfmisc_1(k2_zfmisc_1(C_454,D_453)))
      | ~ v1_funct_1(F_452)
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_456,B_455)))
      | ~ v1_funct_1(E_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3520,plain,(
    ! [A_456,B_455,E_451] :
      ( k1_partfun1(A_456,B_455,k2_struct_0('#skF_1'),'#skF_3',E_451,'#skF_3') = k5_relat_1(E_451,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_456,B_455)))
      | ~ v1_funct_1(E_451) ) ),
    inference(resolution,[status(thm)],[c_3344,c_3516])).

tff(c_3525,plain,(
    ! [A_457,B_458,E_459] :
      ( k1_partfun1(A_457,B_458,k2_struct_0('#skF_1'),'#skF_3',E_459,'#skF_3') = k5_relat_1(E_459,'#skF_3')
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(A_457,B_458)))
      | ~ v1_funct_1(E_459) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3520])).

tff(c_3595,plain,(
    ! [B_474,A_475,C_476] :
      ( k1_partfun1(B_474,A_475,k2_struct_0('#skF_1'),'#skF_3',k2_funct_1(C_476),'#skF_3') = k5_relat_1(k2_funct_1(C_476),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_476))
      | k2_relset_1(A_475,B_474,C_476) != B_474
      | ~ v2_funct_1(C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(k2_zfmisc_1(A_475,B_474)))
      | ~ v1_funct_2(C_476,A_475,B_474)
      | ~ v1_funct_1(C_476) ) ),
    inference(resolution,[status(thm)],[c_32,c_3525])).

tff(c_3601,plain,
    ( k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3344,c_3595])).

tff(c_3605,plain,(
    k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3347,c_48,c_3345,c_3389,c_3601])).

tff(c_3442,plain,(
    ! [A_442,B_443,C_444] :
      ( k2_tops_2(A_442,B_443,C_444) = k2_funct_1(C_444)
      | ~ v2_funct_1(C_444)
      | k2_relset_1(A_442,B_443,C_444) != B_443
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443)))
      | ~ v1_funct_2(C_444,A_442,B_443)
      | ~ v1_funct_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3445,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3344,c_3442])).

tff(c_3448,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3347,c_3345,c_48,c_3445])).

tff(c_3349,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_3216])).

tff(c_3441,plain,(
    k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3349,c_3349,c_3349,c_3349,c_2316])).

tff(c_3449,plain,(
    k1_partfun1('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_3',k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3448,c_3441])).

tff(c_3606,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3605,c_3449])).

tff(c_3613,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3606])).

tff(c_3615,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56,c_48,c_3613])).

tff(c_3654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3639,c_3615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.22  
% 6.00/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.22  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k1_partfun1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.00/2.22  
% 6.00/2.22  %Foreground sorts:
% 6.00/2.22  
% 6.00/2.22  
% 6.00/2.22  %Background operators:
% 6.00/2.22  
% 6.00/2.22  
% 6.00/2.22  %Foreground operators:
% 6.00/2.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.00/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.00/2.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.00/2.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.00/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.00/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.00/2.22  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.00/2.22  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.00/2.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.00/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.22  tff('#skF_1', type, '#skF_1': $i).
% 6.00/2.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.00/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.00/2.22  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.00/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.00/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.00/2.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.00/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.00/2.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.00/2.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.00/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.22  
% 6.00/2.26  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.00/2.26  tff(f_157, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_partfun1(u1_struct_0(A), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), C, k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k6_partfun1(k1_relset_1(u1_struct_0(A), u1_struct_0(B), C))) & (k1_partfun1(u1_struct_0(B), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), C) = k6_partfun1(k2_relset_1(u1_struct_0(A), u1_struct_0(B), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_2)).
% 6.00/2.26  tff(f_124, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.00/2.26  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.00/2.26  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.00/2.26  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.00/2.26  tff(f_104, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.00/2.26  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.00/2.26  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.00/2.26  tff(f_88, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.00/2.26  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.00/2.26  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.00/2.26  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 6.00/2.26  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.00/2.26  tff(c_60, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_74, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.00/2.26  tff(c_82, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_74])).
% 6.00/2.26  tff(c_58, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_81, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_74])).
% 6.00/2.26  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_52])).
% 6.00/2.26  tff(c_98, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.00/2.26  tff(c_101, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_92, c_98])).
% 6.00/2.26  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_101])).
% 6.00/2.26  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_48, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_54, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_91, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_54])).
% 6.00/2.26  tff(c_123, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.00/2.26  tff(c_127, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_123])).
% 6.00/2.26  tff(c_2339, plain, (![B_327, A_328, C_329]: (k1_xboole_0=B_327 | k1_relset_1(A_328, B_327, C_329)=A_328 | ~v1_funct_2(C_329, A_328, B_327) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_328, B_327))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.00/2.26  tff(c_2342, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_92, c_2339])).
% 6.00/2.26  tff(c_2345, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_127, c_2342])).
% 6.00/2.26  tff(c_2346, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2345])).
% 6.00/2.26  tff(c_2351, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_91])).
% 6.00/2.26  tff(c_2350, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_92])).
% 6.00/2.26  tff(c_50, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_93, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_50])).
% 6.00/2.26  tff(c_2349, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_93])).
% 6.00/2.26  tff(c_2398, plain, (![C_333, A_334, B_335]: (v1_funct_1(k2_funct_1(C_333)) | k2_relset_1(A_334, B_335, C_333)!=B_335 | ~v2_funct_1(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))) | ~v1_funct_2(C_333, A_334, B_335) | ~v1_funct_1(C_333))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_2401, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2350, c_2398])).
% 6.00/2.26  tff(c_2404, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2351, c_48, c_2349, c_2401])).
% 6.00/2.26  tff(c_2510, plain, (![B_357, C_358, A_359]: (k6_partfun1(B_357)=k5_relat_1(k2_funct_1(C_358), C_358) | k1_xboole_0=B_357 | ~v2_funct_1(C_358) | k2_relset_1(A_359, B_357, C_358)!=B_357 | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_357))) | ~v1_funct_2(C_358, A_359, B_357) | ~v1_funct_1(C_358))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.00/2.26  tff(c_2514, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2350, c_2510])).
% 6.00/2.26  tff(c_2518, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2351, c_2349, c_48, c_2514])).
% 6.00/2.26  tff(c_2519, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2518])).
% 6.00/2.26  tff(c_2529, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_2351])).
% 6.00/2.26  tff(c_2527, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_2350])).
% 6.00/2.26  tff(c_18, plain, (![C_13, A_11]: (k1_xboole_0=C_13 | ~v1_funct_2(C_13, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.00/2.26  tff(c_2575, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0) | k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2527, c_18])).
% 6.00/2.26  tff(c_2611, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2529, c_2575])).
% 6.00/2.26  tff(c_2627, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2611])).
% 6.00/2.26  tff(c_2633, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2529])).
% 6.00/2.26  tff(c_2528, plain, (k2_relset_1(k1_relat_1('#skF_3'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_2519, c_2349])).
% 6.00/2.26  tff(c_2632, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2528])).
% 6.00/2.26  tff(c_2405, plain, (![C_336, B_337, A_338]: (v1_funct_2(k2_funct_1(C_336), B_337, A_338) | k2_relset_1(A_338, B_337, C_336)!=B_337 | ~v2_funct_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))) | ~v1_funct_2(C_336, A_338, B_337) | ~v1_funct_1(C_336))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_2408, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2350, c_2405])).
% 6.00/2.26  tff(c_2411, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2351, c_48, c_2349, c_2408])).
% 6.00/2.26  tff(c_2525, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_2411])).
% 6.00/2.26  tff(c_2631, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2525])).
% 6.00/2.26  tff(c_2628, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2527])).
% 6.00/2.26  tff(c_2446, plain, (![C_351, B_352, A_353]: (m1_subset_1(k2_funct_1(C_351), k1_zfmisc_1(k2_zfmisc_1(B_352, A_353))) | k2_relset_1(A_353, B_352, C_351)!=B_352 | ~v2_funct_1(C_351) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_353, B_352))) | ~v1_funct_2(C_351, A_353, B_352) | ~v1_funct_1(C_351))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_14, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.00/2.26  tff(c_2495, plain, (![B_352, A_353, C_351]: (k1_relset_1(B_352, A_353, k2_funct_1(C_351))=k1_relat_1(k2_funct_1(C_351)) | k2_relset_1(A_353, B_352, C_351)!=B_352 | ~v2_funct_1(C_351) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_353, B_352))) | ~v1_funct_2(C_351, A_353, B_352) | ~v1_funct_1(C_351))), inference(resolution, [status(thm)], [c_2446, c_14])).
% 6.00/2.26  tff(c_2667, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2628, c_2495])).
% 6.00/2.26  tff(c_2709, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2633, c_48, c_2632, c_2667])).
% 6.00/2.26  tff(c_24, plain, (![B_12, C_13]: (k1_relset_1(k1_xboole_0, B_12, C_13)=k1_xboole_0 | ~v1_funct_2(C_13, k1_xboole_0, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.00/2.26  tff(c_2797, plain, (![A_371, C_372]: (k1_relset_1(k1_xboole_0, A_371, k2_funct_1(C_372))=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_372), k1_xboole_0, A_371) | k2_relset_1(A_371, k1_xboole_0, C_372)!=k1_xboole_0 | ~v2_funct_1(C_372) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_371, k1_xboole_0))) | ~v1_funct_2(C_372, A_371, k1_xboole_0) | ~v1_funct_1(C_372))), inference(resolution, [status(thm)], [c_2446, c_24])).
% 6.00/2.26  tff(c_2800, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2628, c_2797])).
% 6.00/2.26  tff(c_2807, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2633, c_48, c_2632, c_2631, c_2709, c_2800])).
% 6.00/2.26  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.00/2.26  tff(c_2813, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2807, c_8])).
% 6.00/2.26  tff(c_2820, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_2813])).
% 6.00/2.26  tff(c_30, plain, (![A_20]: (k6_relat_1(A_20)=k6_partfun1(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.00/2.26  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.00/2.26  tff(c_63, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 6.00/2.26  tff(c_2429, plain, (![C_345, B_346, E_342, A_347, F_343, D_344]: (k1_partfun1(A_347, B_346, C_345, D_344, E_342, F_343)=k5_relat_1(E_342, F_343) | ~m1_subset_1(F_343, k1_zfmisc_1(k2_zfmisc_1(C_345, D_344))) | ~v1_funct_1(F_343) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(A_347, B_346))) | ~v1_funct_1(E_342))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.00/2.26  tff(c_2431, plain, (![A_347, B_346, E_342]: (k1_partfun1(A_347, B_346, k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), E_342, '#skF_3')=k5_relat_1(E_342, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(A_347, B_346))) | ~v1_funct_1(E_342))), inference(resolution, [status(thm)], [c_2350, c_2429])).
% 6.00/2.26  tff(c_2434, plain, (![A_347, B_346, E_342]: (k1_partfun1(A_347, B_346, k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), E_342, '#skF_3')=k5_relat_1(E_342, '#skF_3') | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(A_347, B_346))) | ~v1_funct_1(E_342))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2431])).
% 6.00/2.26  tff(c_2485, plain, (![B_352, A_353, C_351]: (k1_partfun1(B_352, A_353, k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_funct_1(C_351), '#skF_3')=k5_relat_1(k2_funct_1(C_351), '#skF_3') | ~v1_funct_1(k2_funct_1(C_351)) | k2_relset_1(A_353, B_352, C_351)!=B_352 | ~v2_funct_1(C_351) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_353, B_352))) | ~v1_funct_2(C_351, A_353, B_352) | ~v1_funct_1(C_351))), inference(resolution, [status(thm)], [c_2446, c_2434])).
% 6.00/2.26  tff(c_2830, plain, (![B_373, A_374, C_375]: (k1_partfun1(B_373, A_374, k1_xboole_0, k1_xboole_0, k2_funct_1(C_375), '#skF_3')=k5_relat_1(k2_funct_1(C_375), '#skF_3') | ~v1_funct_1(k2_funct_1(C_375)) | k2_relset_1(A_374, B_373, C_375)!=B_373 | ~v2_funct_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_374, B_373))) | ~v1_funct_2(C_375, A_374, B_373) | ~v1_funct_1(C_375))), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2519, c_2485])).
% 6.00/2.26  tff(c_2833, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2628, c_2830])).
% 6.00/2.26  tff(c_2839, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2633, c_48, c_2632, c_2404, c_2833])).
% 6.00/2.26  tff(c_2412, plain, (![A_339, B_340, C_341]: (k2_tops_2(A_339, B_340, C_341)=k2_funct_1(C_341) | ~v2_funct_1(C_341) | k2_relset_1(A_339, B_340, C_341)!=B_340 | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~v1_funct_2(C_341, A_339, B_340) | ~v1_funct_1(C_341))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.00/2.26  tff(c_2415, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2350, c_2412])).
% 6.00/2.26  tff(c_2418, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2351, c_2349, c_48, c_2415])).
% 6.00/2.26  tff(c_12, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.00/2.26  tff(c_62, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 6.00/2.26  tff(c_156, plain, (![B_55, A_56, C_57]: (k1_xboole_0=B_55 | k1_relset_1(A_56, B_55, C_57)=A_56 | ~v1_funct_2(C_57, A_56, B_55) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.00/2.26  tff(c_159, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_92, c_156])).
% 6.00/2.26  tff(c_162, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_127, c_159])).
% 6.00/2.26  tff(c_163, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_162])).
% 6.00/2.26  tff(c_167, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_91])).
% 6.00/2.26  tff(c_165, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_93])).
% 6.00/2.26  tff(c_166, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_92])).
% 6.00/2.26  tff(c_317, plain, (![B_85, C_86, A_87]: (k6_partfun1(B_85)=k5_relat_1(k2_funct_1(C_86), C_86) | k1_xboole_0=B_85 | ~v2_funct_1(C_86) | k2_relset_1(A_87, B_85, C_86)!=B_85 | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_85))) | ~v1_funct_2(C_86, A_87, B_85) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.00/2.26  tff(c_321, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_166, c_317])).
% 6.00/2.26  tff(c_325, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_167, c_165, c_48, c_321])).
% 6.00/2.26  tff(c_326, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_325])).
% 6.00/2.26  tff(c_335, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_326, c_167])).
% 6.00/2.26  tff(c_333, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_166])).
% 6.00/2.26  tff(c_387, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0) | k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_333, c_18])).
% 6.00/2.26  tff(c_427, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_335, c_387])).
% 6.00/2.26  tff(c_433, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_427])).
% 6.00/2.26  tff(c_439, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_433, c_335])).
% 6.00/2.26  tff(c_332, plain, (k2_relset_1(k1_relat_1('#skF_3'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_165])).
% 6.00/2.26  tff(c_437, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_433, c_332])).
% 6.00/2.26  tff(c_210, plain, (![C_61, A_62, B_63]: (v1_funct_1(k2_funct_1(C_61)) | k2_relset_1(A_62, B_63, C_61)!=B_63 | ~v2_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_2(C_61, A_62, B_63) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_213, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_166, c_210])).
% 6.00/2.26  tff(c_216, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_167, c_48, c_165, c_213])).
% 6.00/2.26  tff(c_434, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_333])).
% 6.00/2.26  tff(c_253, plain, (![C_79, B_80, A_81]: (m1_subset_1(k2_funct_1(C_79), k1_zfmisc_1(k2_zfmisc_1(B_80, A_81))) | k2_relset_1(A_81, B_80, C_79)!=B_80 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_28, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (k1_partfun1(A_14, B_15, C_16, D_17, E_18, F_19)=k5_relat_1(E_18, F_19) | ~m1_subset_1(F_19, k1_zfmisc_1(k2_zfmisc_1(C_16, D_17))) | ~v1_funct_1(F_19) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_1(E_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.00/2.26  tff(c_686, plain, (![B_115, A_118, B_116, C_117, E_113, A_114]: (k1_partfun1(A_118, B_116, B_115, A_114, E_113, k2_funct_1(C_117))=k5_relat_1(E_113, k2_funct_1(C_117)) | ~v1_funct_1(k2_funct_1(C_117)) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_118, B_116))) | ~v1_funct_1(E_113) | k2_relset_1(A_114, B_115, C_117)!=B_115 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_2(C_117, A_114, B_115) | ~v1_funct_1(C_117))), inference(resolution, [status(thm)], [c_253, c_28])).
% 6.00/2.26  tff(c_688, plain, (![B_115, A_114, C_117]: (k1_partfun1(k1_xboole_0, k1_xboole_0, B_115, A_114, '#skF_3', k2_funct_1(C_117))=k5_relat_1('#skF_3', k2_funct_1(C_117)) | ~v1_funct_1(k2_funct_1(C_117)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_114, B_115, C_117)!=B_115 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_2(C_117, A_114, B_115) | ~v1_funct_1(C_117))), inference(resolution, [status(thm)], [c_434, c_686])).
% 6.00/2.26  tff(c_695, plain, (![B_119, A_120, C_121]: (k1_partfun1(k1_xboole_0, k1_xboole_0, B_119, A_120, '#skF_3', k2_funct_1(C_121))=k5_relat_1('#skF_3', k2_funct_1(C_121)) | ~v1_funct_1(k2_funct_1(C_121)) | k2_relset_1(A_120, B_119, C_121)!=B_119 | ~v2_funct_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(C_121, A_120, B_119) | ~v1_funct_1(C_121))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_688])).
% 6.00/2.26  tff(c_698, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_434, c_695])).
% 6.00/2.26  tff(c_704, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_439, c_48, c_437, c_216, c_698])).
% 6.00/2.26  tff(c_224, plain, (![A_67, B_68, C_69]: (k2_tops_2(A_67, B_68, C_69)=k2_funct_1(C_69) | ~v2_funct_1(C_69) | k2_relset_1(A_67, B_68, C_69)!=B_68 | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(C_69, A_67, B_68) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.00/2.26  tff(c_227, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_166, c_224])).
% 6.00/2.26  tff(c_230, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_167, c_165, c_48, c_227])).
% 6.00/2.26  tff(c_46, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.00/2.26  tff(c_61, plain, (k1_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_3', k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46])).
% 6.00/2.26  tff(c_133, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2')) | k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_82, c_82, c_82, c_82, c_81, c_81, c_81, c_81, c_82, c_82, c_82, c_81, c_81, c_81, c_61])).
% 6.00/2.26  tff(c_134, plain, (k1_partfun1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_133])).
% 6.00/2.26  tff(c_209, plain, (k1_partfun1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), '#skF_3', k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_163, c_163, c_134])).
% 6.00/2.26  tff(c_231, plain, (k1_partfun1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_209])).
% 6.00/2.26  tff(c_329, plain, (k1_partfun1(k1_relat_1('#skF_3'), k1_xboole_0, k1_xboole_0, k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_231])).
% 6.00/2.26  tff(c_572, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_433, c_433, c_433, c_329])).
% 6.00/2.26  tff(c_706, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_704, c_572])).
% 6.00/2.26  tff(c_713, plain, (k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1(k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_706])).
% 6.00/2.26  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_433, c_713])).
% 6.00/2.26  tff(c_717, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_427])).
% 6.00/2.26  tff(c_736, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_335])).
% 6.00/2.26  tff(c_734, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_717, c_717, c_332])).
% 6.00/2.26  tff(c_730, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_333])).
% 6.00/2.26  tff(c_1003, plain, (![B_163, A_165, A_161, C_164, B_162, E_160]: (k1_partfun1(A_165, B_163, B_162, A_161, E_160, k2_funct_1(C_164))=k5_relat_1(E_160, k2_funct_1(C_164)) | ~v1_funct_1(k2_funct_1(C_164)) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_165, B_163))) | ~v1_funct_1(E_160) | k2_relset_1(A_161, B_162, C_164)!=B_162 | ~v2_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_2(C_164, A_161, B_162) | ~v1_funct_1(C_164))), inference(resolution, [status(thm)], [c_253, c_28])).
% 6.00/2.26  tff(c_1005, plain, (![B_162, A_161, C_164]: (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', B_162, A_161, '#skF_3', k2_funct_1(C_164))=k5_relat_1('#skF_3', k2_funct_1(C_164)) | ~v1_funct_1(k2_funct_1(C_164)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_161, B_162, C_164)!=B_162 | ~v2_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_2(C_164, A_161, B_162) | ~v1_funct_1(C_164))), inference(resolution, [status(thm)], [c_730, c_1003])).
% 6.00/2.26  tff(c_1013, plain, (![B_166, A_167, C_168]: (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', B_166, A_167, '#skF_3', k2_funct_1(C_168))=k5_relat_1('#skF_3', k2_funct_1(C_168)) | ~v1_funct_1(k2_funct_1(C_168)) | k2_relset_1(A_167, B_166, C_168)!=B_166 | ~v2_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))) | ~v1_funct_2(C_168, A_167, B_166) | ~v1_funct_1(C_168))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1005])).
% 6.00/2.26  tff(c_1016, plain, (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3', k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_730, c_1013])).
% 6.00/2.26  tff(c_1022, plain, (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3', k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_736, c_48, c_734, c_216, c_1016])).
% 6.00/2.26  tff(c_842, plain, (k1_partfun1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3', k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_717, c_329])).
% 6.00/2.26  tff(c_1024, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_842])).
% 6.00/2.26  tff(c_1031, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_1024])).
% 6.00/2.26  tff(c_1035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_1031])).
% 6.00/2.26  tff(c_1037, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_325])).
% 6.00/2.26  tff(c_217, plain, (![C_64, B_65, A_66]: (v1_funct_2(k2_funct_1(C_64), B_65, A_66) | k2_relset_1(A_66, B_65, C_64)!=B_65 | ~v2_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))) | ~v1_funct_2(C_64, A_66, B_65) | ~v1_funct_1(C_64))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_220, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_166, c_217])).
% 6.00/2.26  tff(c_223, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_167, c_48, c_165, c_220])).
% 6.00/2.26  tff(c_1100, plain, (![B_172, A_173, C_174]: (k1_relset_1(B_172, A_173, k2_funct_1(C_174))=k1_relat_1(k2_funct_1(C_174)) | k2_relset_1(A_173, B_172, C_174)!=B_172 | ~v2_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))) | ~v1_funct_2(C_174, A_173, B_172) | ~v1_funct_1(C_174))), inference(resolution, [status(thm)], [c_253, c_14])).
% 6.00/2.26  tff(c_1106, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_166, c_1100])).
% 6.00/2.26  tff(c_1110, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_167, c_48, c_165, c_1106])).
% 6.00/2.26  tff(c_26, plain, (![B_12, A_11, C_13]: (k1_xboole_0=B_12 | k1_relset_1(A_11, B_12, C_13)=A_11 | ~v1_funct_2(C_13, A_11, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.00/2.26  tff(c_1127, plain, (![A_179, B_180, C_181]: (k1_xboole_0=A_179 | k1_relset_1(B_180, A_179, k2_funct_1(C_181))=B_180 | ~v1_funct_2(k2_funct_1(C_181), B_180, A_179) | k2_relset_1(A_179, B_180, C_181)!=B_180 | ~v2_funct_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(C_181, A_179, B_180) | ~v1_funct_1(C_181))), inference(resolution, [status(thm)], [c_253, c_26])).
% 6.00/2.26  tff(c_1133, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_166, c_1127])).
% 6.00/2.26  tff(c_1137, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_167, c_48, c_165, c_223, c_1110, c_1133])).
% 6.00/2.26  tff(c_1138, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1137])).
% 6.00/2.26  tff(c_1143, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1138, c_8])).
% 6.00/2.26  tff(c_1150, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_1143])).
% 6.00/2.26  tff(c_1176, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_167])).
% 6.00/2.26  tff(c_1174, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_166])).
% 6.00/2.26  tff(c_1173, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1150, c_165])).
% 6.00/2.26  tff(c_1058, plain, (![A_169, C_170, B_171]: (k6_partfun1(A_169)=k5_relat_1(C_170, k2_funct_1(C_170)) | k1_xboole_0=B_171 | ~v2_funct_1(C_170) | k2_relset_1(A_169, B_171, C_170)!=B_171 | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_171))) | ~v1_funct_2(C_170, A_169, B_171) | ~v1_funct_1(C_170))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.00/2.26  tff(c_1062, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_struct_0('#skF_2')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_166, c_1058])).
% 6.00/2.26  tff(c_1066, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_167, c_165, c_48, c_1062])).
% 6.00/2.26  tff(c_1067, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1037, c_1066])).
% 6.00/2.26  tff(c_1311, plain, (![E_188, B_191, A_193, B_190, A_189, C_192]: (k1_partfun1(A_193, B_191, B_190, A_189, E_188, k2_funct_1(C_192))=k5_relat_1(E_188, k2_funct_1(C_192)) | ~v1_funct_1(k2_funct_1(C_192)) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_193, B_191))) | ~v1_funct_1(E_188) | k2_relset_1(A_189, B_190, C_192)!=B_190 | ~v2_funct_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_2(C_192, A_189, B_190) | ~v1_funct_1(C_192))), inference(resolution, [status(thm)], [c_253, c_28])).
% 6.00/2.26  tff(c_1313, plain, (![B_190, A_189, C_192]: (k1_partfun1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), B_190, A_189, '#skF_3', k2_funct_1(C_192))=k5_relat_1('#skF_3', k2_funct_1(C_192)) | ~v1_funct_1(k2_funct_1(C_192)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_189, B_190, C_192)!=B_190 | ~v2_funct_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_2(C_192, A_189, B_190) | ~v1_funct_1(C_192))), inference(resolution, [status(thm)], [c_1174, c_1311])).
% 6.00/2.26  tff(c_1347, plain, (![B_200, A_201, C_202]: (k1_partfun1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), B_200, A_201, '#skF_3', k2_funct_1(C_202))=k5_relat_1('#skF_3', k2_funct_1(C_202)) | ~v1_funct_1(k2_funct_1(C_202)) | k2_relset_1(A_201, B_200, C_202)!=B_200 | ~v2_funct_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))) | ~v1_funct_2(C_202, A_201, B_200) | ~v1_funct_1(C_202))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1313])).
% 6.00/2.26  tff(c_1170, plain, (k1_partfun1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1150, c_231])).
% 6.00/2.26  tff(c_1353, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1347, c_1170])).
% 6.00/2.26  tff(c_1360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1176, c_1174, c_48, c_1173, c_216, c_1067, c_1353])).
% 6.00/2.26  tff(c_1361, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1137])).
% 6.00/2.26  tff(c_1373, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_167])).
% 6.00/2.26  tff(c_1370, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_165])).
% 6.00/2.26  tff(c_1369, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_223])).
% 6.00/2.26  tff(c_1371, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_166])).
% 6.00/2.26  tff(c_301, plain, (![C_79, B_80]: (k2_funct_1(C_79)=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_79), B_80, k1_xboole_0) | k1_xboole_0=B_80 | k2_relset_1(k1_xboole_0, B_80, C_79)!=B_80 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_80))) | ~v1_funct_2(C_79, k1_xboole_0, B_80) | ~v1_funct_1(C_79))), inference(resolution, [status(thm)], [c_253, c_18])).
% 6.00/2.26  tff(c_1428, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_xboole_0) | k2_struct_0('#skF_2')=k1_xboole_0 | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1371, c_301])).
% 6.00/2.26  tff(c_1477, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1373, c_48, c_1370, c_1369, c_1428])).
% 6.00/2.26  tff(c_1478, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1037, c_1477])).
% 6.00/2.26  tff(c_1367, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_1361, c_1361, c_231])).
% 6.00/2.26  tff(c_1612, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k1_xboole_0)!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1367])).
% 6.00/2.26  tff(c_1538, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_216])).
% 6.00/2.26  tff(c_1364, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_1067])).
% 6.00/2.26  tff(c_1533, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1364])).
% 6.00/2.26  tff(c_1524, plain, (![A_207, B_208, E_206, B_209, C_210, A_211]: (k1_partfun1(A_211, B_209, B_208, A_207, E_206, k2_funct_1(C_210))=k5_relat_1(E_206, k2_funct_1(C_210)) | ~v1_funct_1(k2_funct_1(C_210)) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_211, B_209))) | ~v1_funct_1(E_206) | k2_relset_1(A_207, B_208, C_210)!=B_208 | ~v2_funct_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(C_210, A_207, B_208) | ~v1_funct_1(C_210))), inference(resolution, [status(thm)], [c_253, c_28])).
% 6.00/2.26  tff(c_1526, plain, (![B_208, A_207, C_210]: (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), B_208, A_207, '#skF_3', k2_funct_1(C_210))=k5_relat_1('#skF_3', k2_funct_1(C_210)) | ~v1_funct_1(k2_funct_1(C_210)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_207, B_208, C_210)!=B_208 | ~v2_funct_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(C_210, A_207, B_208) | ~v1_funct_1(C_210))), inference(resolution, [status(thm)], [c_1371, c_1524])).
% 6.00/2.26  tff(c_1811, plain, (![B_233, A_234, C_235]: (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), B_233, A_234, '#skF_3', k2_funct_1(C_235))=k5_relat_1('#skF_3', k2_funct_1(C_235)) | ~v1_funct_1(k2_funct_1(C_235)) | k2_relset_1(A_234, B_233, C_235)!=B_233 | ~v2_funct_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_234, B_233))) | ~v1_funct_2(C_235, A_234, B_233) | ~v1_funct_1(C_235))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1526])).
% 6.00/2.26  tff(c_1817, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1371, c_1811])).
% 6.00/2.26  tff(c_1826, plain, (k1_partfun1(k1_xboole_0, k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k1_xboole_0, '#skF_3', k1_xboole_0)=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1373, c_48, c_1370, c_1538, c_1478, c_1533, c_1478, c_1478, c_1817])).
% 6.00/2.26  tff(c_1828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1612, c_1826])).
% 6.00/2.26  tff(c_1829, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_162])).
% 6.00/2.26  tff(c_1834, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1829, c_91])).
% 6.00/2.26  tff(c_1833, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1829, c_92])).
% 6.00/2.26  tff(c_1861, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1833, c_18])).
% 6.00/2.26  tff(c_1877, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1834, c_1861])).
% 6.00/2.26  tff(c_1883, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1877])).
% 6.00/2.26  tff(c_1830, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_162])).
% 6.00/2.26  tff(c_1890, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1830])).
% 6.00/2.26  tff(c_1889, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1834])).
% 6.00/2.26  tff(c_1886, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1833])).
% 6.00/2.26  tff(c_1916, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1886, c_24])).
% 6.00/2.26  tff(c_1941, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_1916])).
% 6.00/2.26  tff(c_1831, plain, (k1_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1829, c_127])).
% 6.00/2.26  tff(c_1887, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1831])).
% 6.00/2.26  tff(c_1956, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1941, c_1887])).
% 6.00/2.26  tff(c_1957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1890, c_1956])).
% 6.00/2.26  tff(c_1958, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1877])).
% 6.00/2.26  tff(c_1964, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1958, c_1834])).
% 6.00/2.26  tff(c_1832, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1829, c_1829, c_93])).
% 6.00/2.26  tff(c_1963, plain, (k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1958, c_1958, c_1832])).
% 6.00/2.26  tff(c_1960, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1958, c_1833])).
% 6.00/2.26  tff(c_36, plain, (![C_23, A_21, B_22]: (v1_funct_1(k2_funct_1(C_23)) | k2_relset_1(A_21, B_22, C_23)!=B_22 | ~v2_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_1992, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1960, c_36])).
% 6.00/2.26  tff(c_2001, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1964, c_48, c_1963, c_1992])).
% 6.00/2.26  tff(c_2077, plain, (![C_273, B_274, A_275]: (m1_subset_1(k2_funct_1(C_273), k1_zfmisc_1(k2_zfmisc_1(B_274, A_275))) | k2_relset_1(A_275, B_274, C_273)!=B_274 | ~v2_funct_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_275, B_274))) | ~v1_funct_2(C_273, A_275, B_274) | ~v1_funct_1(C_273))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.26  tff(c_2284, plain, (![C_312, A_315, A_314, B_311, E_310, B_313]: (k1_partfun1(A_314, B_313, B_311, A_315, E_310, k2_funct_1(C_312))=k5_relat_1(E_310, k2_funct_1(C_312)) | ~v1_funct_1(k2_funct_1(C_312)) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(A_314, B_313))) | ~v1_funct_1(E_310) | k2_relset_1(A_315, B_311, C_312)!=B_311 | ~v2_funct_1(C_312) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_315, B_311))) | ~v1_funct_2(C_312, A_315, B_311) | ~v1_funct_1(C_312))), inference(resolution, [status(thm)], [c_2077, c_28])).
% 6.00/2.26  tff(c_2288, plain, (![B_311, A_315, C_312]: (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', B_311, A_315, '#skF_3', k2_funct_1(C_312))=k5_relat_1('#skF_3', k2_funct_1(C_312)) | ~v1_funct_1(k2_funct_1(C_312)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_315, B_311, C_312)!=B_311 | ~v2_funct_1(C_312) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_315, B_311))) | ~v1_funct_2(C_312, A_315, B_311) | ~v1_funct_1(C_312))), inference(resolution, [status(thm)], [c_1960, c_2284])).
% 6.00/2.26  tff(c_2293, plain, (![B_316, A_317, C_318]: (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', B_316, A_317, '#skF_3', k2_funct_1(C_318))=k5_relat_1('#skF_3', k2_funct_1(C_318)) | ~v1_funct_1(k2_funct_1(C_318)) | k2_relset_1(A_317, B_316, C_318)!=B_316 | ~v2_funct_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_317, B_316))) | ~v1_funct_2(C_318, A_317, B_316) | ~v1_funct_1(C_318))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2288])).
% 6.00/2.26  tff(c_2299, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1960, c_2293])).
% 6.00/2.26  tff(c_2303, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1964, c_48, c_1963, c_2001, c_2299])).
% 6.00/2.26  tff(c_2043, plain, (![A_258, B_259, C_260]: (k2_tops_2(A_258, B_259, C_260)=k2_funct_1(C_260) | ~v2_funct_1(C_260) | k2_relset_1(A_258, B_259, C_260)!=B_259 | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(C_260, A_258, B_259) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.00/2.26  tff(c_2046, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1960, c_2043])).
% 6.00/2.26  tff(c_2049, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1964, c_1963, c_48, c_2046])).
% 6.00/2.26  tff(c_1966, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1958, c_1829])).
% 6.00/2.26  tff(c_2006, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_1966, c_1966, c_134])).
% 6.00/2.26  tff(c_2050, plain, (k1_partfun1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_2006])).
% 6.00/2.26  tff(c_2304, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2303, c_2050])).
% 6.00/2.26  tff(c_2311, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_2304])).
% 6.00/2.26  tff(c_2315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_2311])).
% 6.00/2.26  tff(c_2316, plain, (k1_partfun1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_133])).
% 6.00/2.26  tff(c_2347, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_2346, c_2346, c_2316])).
% 6.00/2.26  tff(c_2419, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2347])).
% 6.00/2.26  tff(c_2523, plain, (k1_partfun1(k1_xboole_0, k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_2519, c_2519, c_2419])).
% 6.00/2.26  tff(c_2760, plain, (k1_partfun1(k1_xboole_0, k1_xboole_0, k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2627, c_2523])).
% 6.00/2.26  tff(c_2845, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_2760])).
% 6.00/2.26  tff(c_2852, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1(k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_2845])).
% 6.00/2.26  tff(c_2855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_2820, c_2852])).
% 6.00/2.26  tff(c_2856, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2611])).
% 6.00/2.26  tff(c_2864, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2529])).
% 6.00/2.26  tff(c_2863, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2856, c_2528])).
% 6.00/2.26  tff(c_2862, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2525])).
% 6.00/2.26  tff(c_2859, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2527])).
% 6.00/2.26  tff(c_2902, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2859, c_2495])).
% 6.00/2.26  tff(c_2925, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2864, c_48, c_2863, c_2902])).
% 6.00/2.26  tff(c_2492, plain, (![A_353, C_351]: (k1_relset_1(k1_xboole_0, A_353, k2_funct_1(C_351))=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_351), k1_xboole_0, A_353) | k2_relset_1(A_353, k1_xboole_0, C_351)!=k1_xboole_0 | ~v2_funct_1(C_351) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_353, k1_xboole_0))) | ~v1_funct_2(C_351, A_353, k1_xboole_0) | ~v1_funct_1(C_351))), inference(resolution, [status(thm)], [c_2446, c_24])).
% 6.00/2.26  tff(c_3019, plain, (![A_391, C_392]: (k1_relset_1('#skF_3', A_391, k2_funct_1(C_392))='#skF_3' | ~v1_funct_2(k2_funct_1(C_392), '#skF_3', A_391) | k2_relset_1(A_391, '#skF_3', C_392)!='#skF_3' | ~v2_funct_1(C_392) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_391, '#skF_3'))) | ~v1_funct_2(C_392, A_391, '#skF_3') | ~v1_funct_1(C_392))), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2856, c_2856, c_2856, c_2856, c_2856, c_2856, c_2492])).
% 6.00/2.26  tff(c_3022, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2859, c_3019])).
% 6.00/2.26  tff(c_3029, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2864, c_48, c_2863, c_2862, c_2925, c_3022])).
% 6.00/2.26  tff(c_3035, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3029, c_8])).
% 6.00/2.26  tff(c_3042, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_3035])).
% 6.00/2.26  tff(c_2866, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2519])).
% 6.00/2.26  tff(c_3114, plain, (![B_408, A_409, C_410]: (k1_partfun1(B_408, A_409, k1_relat_1('#skF_3'), '#skF_3', k2_funct_1(C_410), '#skF_3')=k5_relat_1(k2_funct_1(C_410), '#skF_3') | ~v1_funct_1(k2_funct_1(C_410)) | k2_relset_1(A_409, B_408, C_410)!=B_408 | ~v2_funct_1(C_410) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))) | ~v1_funct_2(C_410, A_409, B_408) | ~v1_funct_1(C_410))), inference(demodulation, [status(thm), theory('equality')], [c_2866, c_2485])).
% 6.00/2.26  tff(c_3117, plain, (k1_partfun1('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2859, c_3114])).
% 6.00/2.26  tff(c_3123, plain, (k1_partfun1('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2864, c_48, c_2863, c_2404, c_3117])).
% 6.00/2.26  tff(c_2962, plain, (k1_partfun1('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2856, c_2856, c_2523])).
% 6.00/2.26  tff(c_3125, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3123, c_2962])).
% 6.00/2.26  tff(c_3132, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_3125])).
% 6.00/2.26  tff(c_3135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_3042, c_3132])).
% 6.00/2.26  tff(c_3136, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2518])).
% 6.00/2.26  tff(c_3141, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k6_partfun1(k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3136, c_63])).
% 6.00/2.26  tff(c_3148, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_3141])).
% 6.00/2.26  tff(c_3152, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3148, c_3136])).
% 6.00/2.26  tff(c_3153, plain, (k1_partfun1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3148, c_2419])).
% 6.00/2.27  tff(c_3212, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2485, c_3153])).
% 6.00/2.27  tff(c_3215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2351, c_2350, c_48, c_2349, c_2404, c_3152, c_3212])).
% 6.00/2.27  tff(c_3216, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2345])).
% 6.00/2.27  tff(c_3221, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3216, c_91])).
% 6.00/2.27  tff(c_3220, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3216, c_92])).
% 6.00/2.27  tff(c_3244, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3220, c_18])).
% 6.00/2.27  tff(c_3260, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3221, c_3244])).
% 6.00/2.27  tff(c_3265, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3260])).
% 6.00/2.27  tff(c_3217, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2345])).
% 6.00/2.27  tff(c_3274, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_3217])).
% 6.00/2.27  tff(c_3273, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_3221])).
% 6.00/2.27  tff(c_3271, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_3220])).
% 6.00/2.27  tff(c_3300, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_3271, c_24])).
% 6.00/2.27  tff(c_3325, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3273, c_3300])).
% 6.00/2.27  tff(c_3261, plain, (k1_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3220, c_14])).
% 6.00/2.27  tff(c_3340, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3325, c_3265, c_3261])).
% 6.00/2.27  tff(c_3341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3274, c_3340])).
% 6.00/2.27  tff(c_3342, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3260])).
% 6.00/2.27  tff(c_3347, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_3221])).
% 6.00/2.27  tff(c_3219, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3216, c_3216, c_93])).
% 6.00/2.27  tff(c_3345, plain, (k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_3342, c_3219])).
% 6.00/2.27  tff(c_3344, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_3220])).
% 6.00/2.27  tff(c_3414, plain, (![C_433, B_434, A_435]: (v1_funct_2(k2_funct_1(C_433), B_434, A_435) | k2_relset_1(A_435, B_434, C_433)!=B_434 | ~v2_funct_1(C_433) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_zfmisc_1(A_435, B_434))) | ~v1_funct_2(C_433, A_435, B_434) | ~v1_funct_1(C_433))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.27  tff(c_3417, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3344, c_3414])).
% 6.00/2.27  tff(c_3420, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3347, c_48, c_3345, c_3417])).
% 6.00/2.27  tff(c_3459, plain, (![C_445, B_446, A_447]: (m1_subset_1(k2_funct_1(C_445), k1_zfmisc_1(k2_zfmisc_1(B_446, A_447))) | k2_relset_1(A_447, B_446, C_445)!=B_446 | ~v2_funct_1(C_445) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_447, B_446))) | ~v1_funct_2(C_445, A_447, B_446) | ~v1_funct_1(C_445))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.27  tff(c_3562, plain, (![B_466, A_467, C_468]: (k1_relset_1(B_466, A_467, k2_funct_1(C_468))=k1_relat_1(k2_funct_1(C_468)) | k2_relset_1(A_467, B_466, C_468)!=B_466 | ~v2_funct_1(C_468) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_467, B_466))) | ~v1_funct_2(C_468, A_467, B_466) | ~v1_funct_1(C_468))), inference(resolution, [status(thm)], [c_3459, c_14])).
% 6.00/2.27  tff(c_3568, plain, (k1_relset_1('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3344, c_3562])).
% 6.00/2.27  tff(c_3572, plain, (k1_relset_1('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3347, c_48, c_3345, c_3568])).
% 6.00/2.27  tff(c_3351, plain, (![B_12, C_13]: (k1_relset_1('#skF_3', B_12, C_13)='#skF_3' | ~v1_funct_2(C_13, '#skF_3', B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_12))))), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_3342, c_3342, c_3342, c_24])).
% 6.00/2.27  tff(c_3616, plain, (![A_477, C_478]: (k1_relset_1('#skF_3', A_477, k2_funct_1(C_478))='#skF_3' | ~v1_funct_2(k2_funct_1(C_478), '#skF_3', A_477) | k2_relset_1(A_477, '#skF_3', C_478)!='#skF_3' | ~v2_funct_1(C_478) | ~m1_subset_1(C_478, k1_zfmisc_1(k2_zfmisc_1(A_477, '#skF_3'))) | ~v1_funct_2(C_478, A_477, '#skF_3') | ~v1_funct_1(C_478))), inference(resolution, [status(thm)], [c_3459, c_3351])).
% 6.00/2.27  tff(c_3623, plain, (k1_relset_1('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3344, c_3616])).
% 6.00/2.27  tff(c_3627, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3347, c_48, c_3345, c_3420, c_3572, c_3623])).
% 6.00/2.27  tff(c_3632, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3627, c_8])).
% 6.00/2.27  tff(c_3639, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_3632])).
% 6.00/2.27  tff(c_3380, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3344, c_36])).
% 6.00/2.27  tff(c_3389, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3347, c_48, c_3345, c_3380])).
% 6.00/2.27  tff(c_32, plain, (![C_23, B_22, A_21]: (m1_subset_1(k2_funct_1(C_23), k1_zfmisc_1(k2_zfmisc_1(B_22, A_21))) | k2_relset_1(A_21, B_22, C_23)!=B_22 | ~v2_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.00/2.27  tff(c_3516, plain, (![C_454, F_452, B_455, A_456, E_451, D_453]: (k1_partfun1(A_456, B_455, C_454, D_453, E_451, F_452)=k5_relat_1(E_451, F_452) | ~m1_subset_1(F_452, k1_zfmisc_1(k2_zfmisc_1(C_454, D_453))) | ~v1_funct_1(F_452) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_456, B_455))) | ~v1_funct_1(E_451))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.00/2.27  tff(c_3520, plain, (![A_456, B_455, E_451]: (k1_partfun1(A_456, B_455, k2_struct_0('#skF_1'), '#skF_3', E_451, '#skF_3')=k5_relat_1(E_451, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_456, B_455))) | ~v1_funct_1(E_451))), inference(resolution, [status(thm)], [c_3344, c_3516])).
% 6.00/2.27  tff(c_3525, plain, (![A_457, B_458, E_459]: (k1_partfun1(A_457, B_458, k2_struct_0('#skF_1'), '#skF_3', E_459, '#skF_3')=k5_relat_1(E_459, '#skF_3') | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(A_457, B_458))) | ~v1_funct_1(E_459))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3520])).
% 6.00/2.27  tff(c_3595, plain, (![B_474, A_475, C_476]: (k1_partfun1(B_474, A_475, k2_struct_0('#skF_1'), '#skF_3', k2_funct_1(C_476), '#skF_3')=k5_relat_1(k2_funct_1(C_476), '#skF_3') | ~v1_funct_1(k2_funct_1(C_476)) | k2_relset_1(A_475, B_474, C_476)!=B_474 | ~v2_funct_1(C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(k2_zfmisc_1(A_475, B_474))) | ~v1_funct_2(C_476, A_475, B_474) | ~v1_funct_1(C_476))), inference(resolution, [status(thm)], [c_32, c_3525])).
% 6.00/2.27  tff(c_3601, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3344, c_3595])).
% 6.00/2.27  tff(c_3605, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3347, c_48, c_3345, c_3389, c_3601])).
% 6.00/2.27  tff(c_3442, plain, (![A_442, B_443, C_444]: (k2_tops_2(A_442, B_443, C_444)=k2_funct_1(C_444) | ~v2_funct_1(C_444) | k2_relset_1(A_442, B_443, C_444)!=B_443 | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))) | ~v1_funct_2(C_444, A_442, B_443) | ~v1_funct_1(C_444))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.00/2.27  tff(c_3445, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3344, c_3442])).
% 6.00/2.27  tff(c_3448, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3347, c_3345, c_48, c_3445])).
% 6.00/2.27  tff(c_3349, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_3216])).
% 6.00/2.27  tff(c_3441, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3349, c_3349, c_3349, c_3349, c_2316])).
% 6.00/2.27  tff(c_3449, plain, (k1_partfun1('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_3', k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3448, c_3441])).
% 6.00/2.27  tff(c_3606, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3605, c_3449])).
% 6.00/2.27  tff(c_3613, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_3606])).
% 6.00/2.27  tff(c_3615, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56, c_48, c_3613])).
% 6.00/2.27  tff(c_3654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3639, c_3615])).
% 6.00/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.27  
% 6.00/2.27  Inference rules
% 6.00/2.27  ----------------------
% 6.00/2.27  #Ref     : 0
% 6.00/2.27  #Sup     : 784
% 6.00/2.27  #Fact    : 0
% 6.00/2.27  #Define  : 0
% 6.00/2.27  #Split   : 16
% 6.00/2.27  #Chain   : 0
% 6.00/2.27  #Close   : 0
% 6.00/2.27  
% 6.00/2.27  Ordering : KBO
% 6.00/2.27  
% 6.00/2.27  Simplification rules
% 6.00/2.27  ----------------------
% 6.00/2.27  #Subsume      : 53
% 6.00/2.27  #Demod        : 1367
% 6.00/2.27  #Tautology    : 506
% 6.00/2.27  #SimpNegUnit  : 29
% 6.00/2.27  #BackRed      : 182
% 6.00/2.27  
% 6.00/2.27  #Partial instantiations: 0
% 6.00/2.27  #Strategies tried      : 1
% 6.00/2.27  
% 6.00/2.27  Timing (in seconds)
% 6.00/2.27  ----------------------
% 6.00/2.27  Preprocessing        : 0.42
% 6.00/2.27  Parsing              : 0.22
% 6.00/2.27  CNF conversion       : 0.03
% 6.00/2.27  Main loop            : 0.94
% 6.00/2.27  Inferencing          : 0.32
% 6.00/2.27  Reduction            : 0.33
% 6.00/2.27  Demodulation         : 0.24
% 6.00/2.27  BG Simplification    : 0.04
% 6.00/2.27  Subsumption          : 0.17
% 6.00/2.27  Abstraction          : 0.05
% 6.00/2.27  MUC search           : 0.00
% 6.00/2.27  Cooper               : 0.00
% 6.00/2.27  Total                : 1.48
% 6.00/2.27  Index Insertion      : 0.00
% 6.00/2.27  Index Deletion       : 0.00
% 6.00/2.27  Index Matching       : 0.00
% 6.00/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
