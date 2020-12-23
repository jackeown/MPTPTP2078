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
% DateTime   : Thu Dec  3 10:23:24 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :  293 (18065 expanded)
%              Number of leaves         :   52 (6018 expanded)
%              Depth                    :   24
%              Number of atoms          :  623 (52073 expanded)
%              Number of equality atoms :  188 (16387 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
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

tff(f_138,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_134,axiom,(
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_68,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_72,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_77,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_85,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_77])).

tff(c_84,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_77])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62])).

tff(c_1932,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_86])).

tff(c_2015,plain,(
    ! [A_271,B_272,C_273] :
      ( k2_relset_1(A_271,B_272,C_273) = k2_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2019,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1932,c_2015])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_98,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_84,c_60])).

tff(c_2020,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2019,c_98])).

tff(c_52,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(k2_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2035,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2020,c_52])).

tff(c_2039,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2035])).

tff(c_2040,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2039])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( v1_relat_1(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1935,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1932,c_10])).

tff(c_1938,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1935])).

tff(c_1955,plain,(
    ! [C_259,A_260,B_261] :
      ( v4_relat_1(C_259,A_260)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1959,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1932,c_1955])).

tff(c_1994,plain,(
    ! [B_267,A_268] :
      ( k1_relat_1(B_267) = A_268
      | ~ v1_partfun1(B_267,A_268)
      | ~ v4_relat_1(B_267,A_268)
      | ~ v1_relat_1(B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1997,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1959,c_1994])).

tff(c_2000,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1997])).

tff(c_2001,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2000])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_87,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64])).

tff(c_96,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_87])).

tff(c_2030,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_96])).

tff(c_2029,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_1932])).

tff(c_2106,plain,(
    ! [C_281,A_282,B_283] :
      ( v1_partfun1(C_281,A_282)
      | ~ v1_funct_2(C_281,A_282,B_283)
      | ~ v1_funct_1(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | v1_xboole_0(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2109,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2029,c_2106])).

tff(c_2112,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2030,c_2109])).

tff(c_2114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2040,c_2001,c_2112])).

tff(c_2115,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2000])).

tff(c_2122,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_1932])).

tff(c_2229,plain,(
    ! [A_289,B_290,C_291] :
      ( k2_relset_1(A_289,B_290,C_291) = k2_relat_1(C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2233,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2122,c_2229])).

tff(c_2123,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_98])).

tff(c_2234,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2233,c_2123])).

tff(c_2124,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_96])).

tff(c_2242,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_2124])).

tff(c_2239,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_2233])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2241,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_2122])).

tff(c_2407,plain,(
    ! [A_310,B_311,C_312] :
      ( k2_tops_2(A_310,B_311,C_312) = k2_funct_1(C_312)
      | ~ v2_funct_1(C_312)
      | k2_relset_1(A_310,B_311,C_312) != B_311
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311)))
      | ~ v1_funct_2(C_312,A_310,B_311)
      | ~ v1_funct_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2410,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2241,c_2407])).

tff(c_2413,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2242,c_2239,c_58,c_2410])).

tff(c_132,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_86])).

tff(c_135,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_132,c_10])).

tff(c_138,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_135])).

tff(c_22,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) = k1_xboole_0
      | k1_relat_1(A_14) != k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_22])).

tff(c_147,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_211,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_215,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_211])).

tff(c_216,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_98])).

tff(c_230,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_52])).

tff(c_234,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_230])).

tff(c_235,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_234])).

tff(c_150,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_154,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_132,c_150])).

tff(c_203,plain,(
    ! [B_74,A_75] :
      ( k1_relat_1(B_74) = A_75
      | ~ v1_partfun1(B_74,A_75)
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_206,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_203])).

tff(c_209,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_206])).

tff(c_210,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_225,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_96])).

tff(c_224,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_132])).

tff(c_330,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_partfun1(C_88,A_89)
      | ~ v1_funct_2(C_88,A_89,B_90)
      | ~ v1_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | v1_xboole_0(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_333,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_224,c_330])).

tff(c_336,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_225,c_333])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_210,c_336])).

tff(c_339,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_345,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_132])).

tff(c_34,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_427,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_345,c_34])).

tff(c_346,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_98])).

tff(c_435,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_346])).

tff(c_347,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_96])).

tff(c_442,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_347])).

tff(c_440,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_427])).

tff(c_441,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_345])).

tff(c_602,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_tops_2(A_115,B_116,C_117) = k2_funct_1(C_117)
      | ~ v2_funct_1(C_117)
      | k2_relset_1(A_115,B_116,C_117) != B_116
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_2(C_117,A_115,B_116)
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_605,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_602])).

tff(c_608,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_442,c_440,c_58,c_605])).

tff(c_56,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_116,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_84,c_84,c_85,c_85,c_84,c_84,c_56])).

tff(c_117,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_344,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_339,c_117])).

tff(c_460,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_435,c_435,c_344])).

tff(c_609,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_460])).

tff(c_352,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_52])).

tff(c_356,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_352])).

tff(c_391,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_614,plain,(
    ! [C_118,B_119,A_120] :
      ( m1_subset_1(k2_funct_1(C_118),k1_zfmisc_1(k2_zfmisc_1(B_119,A_120)))
      | k2_relset_1(A_120,B_119,C_118) != B_119
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(C_118,A_120,B_119)
      | ~ v1_funct_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_641,plain,(
    ! [C_118,B_119,A_120] :
      ( v1_relat_1(k2_funct_1(C_118))
      | ~ v1_relat_1(k2_zfmisc_1(B_119,A_120))
      | k2_relset_1(A_120,B_119,C_118) != B_119
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(C_118,A_120,B_119)
      | ~ v1_funct_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_614,c_10])).

tff(c_653,plain,(
    ! [C_121,A_122,B_123] :
      ( v1_relat_1(k2_funct_1(C_121))
      | k2_relset_1(A_122,B_123,C_121) != B_123
      | ~ v2_funct_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_2(C_121,A_122,B_123)
      | ~ v1_funct_1(C_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_641])).

tff(c_659,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_653])).

tff(c_663,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_442,c_58,c_440,c_659])).

tff(c_30,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_673,plain,(
    ! [C_124,B_125,A_126] :
      ( v4_relat_1(k2_funct_1(C_124),B_125)
      | k2_relset_1(A_126,B_125,C_124) != B_125
      | ~ v2_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2(C_124,A_126,B_125)
      | ~ v1_funct_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_614,c_30])).

tff(c_679,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_673])).

tff(c_683,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_442,c_58,c_440,c_679])).

tff(c_42,plain,(
    ! [B_33,A_32] :
      ( k1_relat_1(B_33) = A_32
      | ~ v1_partfun1(B_33,A_32)
      | ~ v4_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_686,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_683,c_42])).

tff(c_692,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_686])).

tff(c_746,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_587,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_funct_1(k2_funct_1(C_107))
      | k2_relset_1(A_108,B_109,C_107) != B_109
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_590,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_587])).

tff(c_593,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_442,c_58,c_440,c_590])).

tff(c_594,plain,(
    ! [C_110,B_111,A_112] :
      ( v1_funct_2(k2_funct_1(C_110),B_111,A_112)
      | k2_relset_1(A_112,B_111,C_110) != B_111
      | ~ v2_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111)))
      | ~ v1_funct_2(C_110,A_112,B_111)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_597,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_594])).

tff(c_600,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_442,c_58,c_440,c_597])).

tff(c_36,plain,(
    ! [C_31,A_28,B_29] :
      ( v1_partfun1(C_31,A_28)
      | ~ v1_funct_2(C_31,A_28,B_29)
      | ~ v1_funct_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_802,plain,(
    ! [C_137,B_138,A_139] :
      ( v1_partfun1(k2_funct_1(C_137),B_138)
      | ~ v1_funct_2(k2_funct_1(C_137),B_138,A_139)
      | ~ v1_funct_1(k2_funct_1(C_137))
      | v1_xboole_0(A_139)
      | k2_relset_1(A_139,B_138,C_137) != B_138
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_2(C_137,A_139,B_138)
      | ~ v1_funct_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_614,c_36])).

tff(c_808,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_802])).

tff(c_812,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_442,c_58,c_440,c_593,c_600,c_808])).

tff(c_814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_746,c_812])).

tff(c_815,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_32,plain,(
    ! [A_22,B_23,C_24] :
      ( k1_relset_1(A_22,B_23,C_24) = k1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_892,plain,(
    ! [B_147,A_148,C_149] :
      ( k1_relset_1(B_147,A_148,k2_funct_1(C_149)) = k1_relat_1(k2_funct_1(C_149))
      | k2_relset_1(A_148,B_147,C_149) != B_147
      | ~ v2_funct_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147)))
      | ~ v1_funct_2(C_149,A_148,B_147)
      | ~ v1_funct_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_614,c_32])).

tff(c_898,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_892])).

tff(c_902,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_442,c_58,c_440,c_815,c_898])).

tff(c_904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_902])).

tff(c_906,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_913,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_906,c_2])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_913])).

tff(c_918,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_1266,plain,(
    ! [A_192,B_193,C_194] :
      ( k2_relset_1(A_192,B_193,C_194) = k2_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1269,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_1266])).

tff(c_1271,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_1269])).

tff(c_1272,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_98])).

tff(c_1287,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_52])).

tff(c_1291,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1287])).

tff(c_1292,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1291])).

tff(c_919,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_937,plain,(
    ! [C_150,A_151,B_152] :
      ( v4_relat_1(C_150,A_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_941,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_132,c_937])).

tff(c_1242,plain,(
    ! [B_187,A_188] :
      ( k1_relat_1(B_187) = A_188
      | ~ v1_partfun1(B_187,A_188)
      | ~ v4_relat_1(B_187,A_188)
      | ~ v1_relat_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1248,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_941,c_1242])).

tff(c_1254,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_919,c_1248])).

tff(c_1255,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1254])).

tff(c_1282,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1272,c_96])).

tff(c_1281,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1272,c_132])).

tff(c_1388,plain,(
    ! [C_200,A_201,B_202] :
      ( v1_partfun1(C_200,A_201)
      | ~ v1_funct_2(C_200,A_201,B_202)
      | ~ v1_funct_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | v1_xboole_0(B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1391,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1281,c_1388])).

tff(c_1394,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1282,c_1391])).

tff(c_1396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1292,c_1255,c_1394])).

tff(c_1397,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1254])).

tff(c_1403,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_132])).

tff(c_1455,plain,(
    ! [A_206,B_207,C_208] :
      ( k2_relset_1(A_206,B_207,C_208) = k2_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1458,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1403,c_1455])).

tff(c_1460,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_1458])).

tff(c_1404,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_98])).

tff(c_1461,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_1404])).

tff(c_1405,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_96])).

tff(c_1470,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1405])).

tff(c_1466,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1460])).

tff(c_1469,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1403])).

tff(c_1659,plain,(
    ! [A_228,B_229,C_230] :
      ( k2_tops_2(A_228,B_229,C_230) = k2_funct_1(C_230)
      | ~ v2_funct_1(C_230)
      | k2_relset_1(A_228,B_229,C_230) != B_229
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_2(C_230,A_228,B_229)
      | ~ v1_funct_1(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1662,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1469,c_1659])).

tff(c_1665,plain,(
    k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1470,c_1466,c_58,c_1662])).

tff(c_1401,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1397,c_117])).

tff(c_1468,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1461,c_1461,c_1401])).

tff(c_1666,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1468])).

tff(c_1671,plain,(
    ! [C_231,B_232,A_233] :
      ( m1_subset_1(k2_funct_1(C_231),k1_zfmisc_1(k2_zfmisc_1(B_232,A_233)))
      | k2_relset_1(A_233,B_232,C_231) != B_232
      | ~ v2_funct_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_233,B_232)))
      | ~ v1_funct_2(C_231,A_233,B_232)
      | ~ v1_funct_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1698,plain,(
    ! [C_231,B_232,A_233] :
      ( v1_relat_1(k2_funct_1(C_231))
      | ~ v1_relat_1(k2_zfmisc_1(B_232,A_233))
      | k2_relset_1(A_233,B_232,C_231) != B_232
      | ~ v2_funct_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_233,B_232)))
      | ~ v1_funct_2(C_231,A_233,B_232)
      | ~ v1_funct_1(C_231) ) ),
    inference(resolution,[status(thm)],[c_1671,c_10])).

tff(c_1710,plain,(
    ! [C_234,A_235,B_236] :
      ( v1_relat_1(k2_funct_1(C_234))
      | k2_relset_1(A_235,B_236,C_234) != B_236
      | ~ v2_funct_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ v1_funct_2(C_234,A_235,B_236)
      | ~ v1_funct_1(C_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1698])).

tff(c_1716,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1469,c_1710])).

tff(c_1720,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1470,c_58,c_1466,c_1716])).

tff(c_1727,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1720,c_22])).

tff(c_1729,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1727])).

tff(c_20,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) = k1_xboole_0
      | k2_relat_1(A_14) != k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1728,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1720,c_20])).

tff(c_1730,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1728])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_927,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_14])).

tff(c_931,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_918,c_927])).

tff(c_1538,plain,(
    ! [B_211,A_212] :
      ( k10_relat_1(B_211,k9_relat_1(B_211,A_212)) = A_212
      | ~ v2_funct_1(B_211)
      | ~ r1_tarski(A_212,k1_relat_1(B_211))
      | ~ v1_funct_1(B_211)
      | ~ v1_relat_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1540,plain,(
    ! [A_212] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_212)) = A_212
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_212,k1_xboole_0)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_1538])).

tff(c_1547,plain,(
    ! [A_213] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_213)) = A_213
      | ~ r1_tarski(A_213,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_66,c_58,c_1540])).

tff(c_1556,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1547])).

tff(c_1564,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1556])).

tff(c_1731,plain,(
    ! [C_237,B_238,A_239] :
      ( v4_relat_1(k2_funct_1(C_237),B_238)
      | k2_relset_1(A_239,B_238,C_237) != B_238
      | ~ v2_funct_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238)))
      | ~ v1_funct_2(C_237,A_239,B_238)
      | ~ v1_funct_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_1671,c_30])).

tff(c_1737,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k1_xboole_0)
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1469,c_1731])).

tff(c_1741,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1470,c_58,c_1466,c_1737])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1747,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1741,c_18])).

tff(c_1754,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_1747])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1769,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_16])).

tff(c_1773,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k1_xboole_0) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_1769])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k9_relat_1(k2_funct_1(B_16),A_15) = k10_relat_1(B_16,A_15)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1778,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3',k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1773,c_24])).

tff(c_1785,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_66,c_58,c_1564,c_1778])).

tff(c_1787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1730,c_1785])).

tff(c_1788,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1728])).

tff(c_1799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1729,c_1788])).

tff(c_1801,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1727])).

tff(c_1903,plain,(
    ! [B_249,A_250,C_251] :
      ( k1_relset_1(B_249,A_250,k2_funct_1(C_251)) = k1_relat_1(k2_funct_1(C_251))
      | k2_relset_1(A_250,B_249,C_251) != B_249
      | ~ v2_funct_1(C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249)))
      | ~ v1_funct_2(C_251,A_250,B_249)
      | ~ v1_funct_1(C_251) ) ),
    inference(resolution,[status(thm)],[c_1671,c_32])).

tff(c_1909,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1469,c_1903])).

tff(c_1913,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1470,c_58,c_1466,c_1801,c_1909])).

tff(c_1915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1666,c_1913])).

tff(c_1916,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_2121,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_2115,c_2115,c_1916])).

tff(c_2320,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_2234,c_2121])).

tff(c_2414,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2413,c_2320])).

tff(c_1962,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1959,c_18])).

tff(c_1965,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1962])).

tff(c_1974,plain,(
    ! [B_262,A_263] :
      ( k2_relat_1(k7_relat_1(B_262,A_263)) = k9_relat_1(B_262,A_263)
      | ~ v1_relat_1(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1983,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1965,c_1974])).

tff(c_1987,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1983])).

tff(c_2117,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_1987])).

tff(c_2315,plain,(
    ! [B_294,A_295] :
      ( k10_relat_1(B_294,k9_relat_1(B_294,A_295)) = A_295
      | ~ v2_funct_1(B_294)
      | ~ r1_tarski(A_295,k1_relat_1(B_294))
      | ~ v1_funct_1(B_294)
      | ~ v1_relat_1(B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2321,plain,(
    ! [B_296] :
      ( k10_relat_1(B_296,k9_relat_1(B_296,k1_relat_1(B_296))) = k1_relat_1(B_296)
      | ~ v2_funct_1(B_296)
      | ~ v1_funct_1(B_296)
      | ~ v1_relat_1(B_296) ) ),
    inference(resolution,[status(thm)],[c_8,c_2315])).

tff(c_2334,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2117,c_2321])).

tff(c_2341,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_66,c_58,c_2334])).

tff(c_2424,plain,(
    ! [C_313,B_314,A_315] :
      ( m1_subset_1(k2_funct_1(C_313),k1_zfmisc_1(k2_zfmisc_1(B_314,A_315)))
      | k2_relset_1(A_315,B_314,C_313) != B_314
      | ~ v2_funct_1(C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_315,B_314)))
      | ~ v1_funct_2(C_313,A_315,B_314)
      | ~ v1_funct_1(C_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2451,plain,(
    ! [C_313,B_314,A_315] :
      ( v1_relat_1(k2_funct_1(C_313))
      | ~ v1_relat_1(k2_zfmisc_1(B_314,A_315))
      | k2_relset_1(A_315,B_314,C_313) != B_314
      | ~ v2_funct_1(C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_315,B_314)))
      | ~ v1_funct_2(C_313,A_315,B_314)
      | ~ v1_funct_1(C_313) ) ),
    inference(resolution,[status(thm)],[c_2424,c_10])).

tff(c_2463,plain,(
    ! [C_316,A_317,B_318] :
      ( v1_relat_1(k2_funct_1(C_316))
      | k2_relset_1(A_317,B_318,C_316) != B_318
      | ~ v2_funct_1(C_316)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318)))
      | ~ v1_funct_2(C_316,A_317,B_318)
      | ~ v1_funct_1(C_316) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2451])).

tff(c_2469,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2241,c_2463])).

tff(c_2473,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2242,c_58,c_2239,c_2469])).

tff(c_2482,plain,(
    ! [C_319,B_320,A_321] :
      ( v4_relat_1(k2_funct_1(C_319),B_320)
      | k2_relset_1(A_321,B_320,C_319) != B_320
      | ~ v2_funct_1(C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_321,B_320)))
      | ~ v1_funct_2(C_319,A_321,B_320)
      | ~ v1_funct_1(C_319) ) ),
    inference(resolution,[status(thm)],[c_2424,c_30])).

tff(c_2488,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2241,c_2482])).

tff(c_2492,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2242,c_58,c_2239,c_2488])).

tff(c_2498,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2492,c_18])).

tff(c_2504,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_2498])).

tff(c_2508,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2504,c_16])).

tff(c_2512,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_2508])).

tff(c_2519,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2512,c_24])).

tff(c_2526,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_66,c_58,c_2341,c_2519])).

tff(c_2627,plain,(
    ! [B_329,A_330,C_331] :
      ( k2_relset_1(B_329,A_330,k2_funct_1(C_331)) = k2_relat_1(k2_funct_1(C_331))
      | k2_relset_1(A_330,B_329,C_331) != B_329
      | ~ v2_funct_1(C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_330,B_329)))
      | ~ v1_funct_2(C_331,A_330,B_329)
      | ~ v1_funct_1(C_331) ) ),
    inference(resolution,[status(thm)],[c_2424,c_34])).

tff(c_2633,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2241,c_2627])).

tff(c_2637,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2242,c_58,c_2239,c_2526,c_2633])).

tff(c_2639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2414,c_2637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/1.93  
% 5.27/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/1.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.27/1.94  
% 5.27/1.94  %Foreground sorts:
% 5.27/1.94  
% 5.27/1.94  
% 5.27/1.94  %Background operators:
% 5.27/1.94  
% 5.27/1.94  
% 5.27/1.94  %Foreground operators:
% 5.27/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.27/1.94  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.27/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.27/1.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.27/1.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.27/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/1.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.27/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.27/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.27/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.27/1.94  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.27/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.27/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.27/1.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.27/1.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.27/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.27/1.94  tff('#skF_1', type, '#skF_1': $i).
% 5.27/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.27/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.27/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.27/1.94  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.27/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/1.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.27/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.27/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.27/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.27/1.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.27/1.94  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.27/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.27/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.27/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.27/1.94  
% 5.27/1.97  tff(f_182, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 5.27/1.97  tff(f_138, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.27/1.97  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.27/1.97  tff(f_146, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.27/1.97  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.27/1.97  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.27/1.97  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.27/1.97  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.27/1.97  tff(f_110, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.27/1.97  tff(f_158, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.27/1.97  tff(f_64, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 5.27/1.97  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.27/1.97  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.27/1.97  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.27/1.97  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.27/1.97  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.27/1.97  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 5.27/1.97  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.27/1.97  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.27/1.97  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 5.27/1.97  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_68, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_72, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_77, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.27/1.97  tff(c_85, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_77])).
% 5.27/1.97  tff(c_84, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_77])).
% 5.27/1.97  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62])).
% 5.27/1.97  tff(c_1932, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_86])).
% 5.27/1.97  tff(c_2015, plain, (![A_271, B_272, C_273]: (k2_relset_1(A_271, B_272, C_273)=k2_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.27/1.97  tff(c_2019, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1932, c_2015])).
% 5.27/1.97  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_98, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_84, c_60])).
% 5.27/1.97  tff(c_2020, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2019, c_98])).
% 5.27/1.97  tff(c_52, plain, (![A_38]: (~v1_xboole_0(k2_struct_0(A_38)) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.27/1.97  tff(c_2035, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2020, c_52])).
% 5.27/1.97  tff(c_2039, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2035])).
% 5.27/1.97  tff(c_2040, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_2039])).
% 5.27/1.97  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.27/1.97  tff(c_10, plain, (![B_6, A_4]: (v1_relat_1(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.27/1.97  tff(c_1935, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1932, c_10])).
% 5.27/1.97  tff(c_1938, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1935])).
% 5.27/1.97  tff(c_1955, plain, (![C_259, A_260, B_261]: (v4_relat_1(C_259, A_260) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/1.97  tff(c_1959, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1932, c_1955])).
% 5.27/1.97  tff(c_1994, plain, (![B_267, A_268]: (k1_relat_1(B_267)=A_268 | ~v1_partfun1(B_267, A_268) | ~v4_relat_1(B_267, A_268) | ~v1_relat_1(B_267))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.27/1.97  tff(c_1997, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1959, c_1994])).
% 5.27/1.97  tff(c_2000, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1997])).
% 5.27/1.97  tff(c_2001, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2000])).
% 5.27/1.97  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_87, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64])).
% 5.27/1.97  tff(c_96, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_87])).
% 5.27/1.97  tff(c_2030, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_96])).
% 5.27/1.97  tff(c_2029, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_1932])).
% 5.27/1.97  tff(c_2106, plain, (![C_281, A_282, B_283]: (v1_partfun1(C_281, A_282) | ~v1_funct_2(C_281, A_282, B_283) | ~v1_funct_1(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | v1_xboole_0(B_283))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.27/1.97  tff(c_2109, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2029, c_2106])).
% 5.27/1.97  tff(c_2112, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2030, c_2109])).
% 5.27/1.97  tff(c_2114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2040, c_2001, c_2112])).
% 5.27/1.97  tff(c_2115, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2000])).
% 5.27/1.97  tff(c_2122, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_1932])).
% 5.27/1.97  tff(c_2229, plain, (![A_289, B_290, C_291]: (k2_relset_1(A_289, B_290, C_291)=k2_relat_1(C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.27/1.97  tff(c_2233, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2122, c_2229])).
% 5.27/1.97  tff(c_2123, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_98])).
% 5.27/1.97  tff(c_2234, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2233, c_2123])).
% 5.27/1.97  tff(c_2124, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_96])).
% 5.27/1.97  tff(c_2242, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_2124])).
% 5.27/1.97  tff(c_2239, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_2233])).
% 5.27/1.97  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_2241, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_2122])).
% 5.27/1.97  tff(c_2407, plain, (![A_310, B_311, C_312]: (k2_tops_2(A_310, B_311, C_312)=k2_funct_1(C_312) | ~v2_funct_1(C_312) | k2_relset_1(A_310, B_311, C_312)!=B_311 | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))) | ~v1_funct_2(C_312, A_310, B_311) | ~v1_funct_1(C_312))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.27/1.97  tff(c_2410, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2241, c_2407])).
% 5.27/1.97  tff(c_2413, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2242, c_2239, c_58, c_2410])).
% 5.27/1.97  tff(c_132, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_86])).
% 5.27/1.97  tff(c_135, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_10])).
% 5.27/1.97  tff(c_138, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_135])).
% 5.27/1.97  tff(c_22, plain, (![A_14]: (k2_relat_1(A_14)=k1_xboole_0 | k1_relat_1(A_14)!=k1_xboole_0 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.27/1.97  tff(c_145, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_22])).
% 5.27/1.97  tff(c_147, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_145])).
% 5.27/1.97  tff(c_211, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.27/1.97  tff(c_215, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_211])).
% 5.27/1.97  tff(c_216, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_98])).
% 5.27/1.97  tff(c_230, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_216, c_52])).
% 5.27/1.97  tff(c_234, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_230])).
% 5.27/1.97  tff(c_235, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_234])).
% 5.27/1.97  tff(c_150, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/1.97  tff(c_154, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_132, c_150])).
% 5.27/1.97  tff(c_203, plain, (![B_74, A_75]: (k1_relat_1(B_74)=A_75 | ~v1_partfun1(B_74, A_75) | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.27/1.97  tff(c_206, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_154, c_203])).
% 5.27/1.97  tff(c_209, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_206])).
% 5.27/1.97  tff(c_210, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_209])).
% 5.27/1.97  tff(c_225, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_96])).
% 5.27/1.97  tff(c_224, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_132])).
% 5.27/1.97  tff(c_330, plain, (![C_88, A_89, B_90]: (v1_partfun1(C_88, A_89) | ~v1_funct_2(C_88, A_89, B_90) | ~v1_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | v1_xboole_0(B_90))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.27/1.97  tff(c_333, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_224, c_330])).
% 5.27/1.97  tff(c_336, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_225, c_333])).
% 5.27/1.97  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_210, c_336])).
% 5.27/1.97  tff(c_339, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_209])).
% 5.27/1.97  tff(c_345, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_132])).
% 5.27/1.97  tff(c_34, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.27/1.97  tff(c_427, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_345, c_34])).
% 5.27/1.97  tff(c_346, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_98])).
% 5.27/1.97  tff(c_435, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_346])).
% 5.27/1.97  tff(c_347, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_96])).
% 5.27/1.97  tff(c_442, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_347])).
% 5.27/1.97  tff(c_440, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_427])).
% 5.27/1.97  tff(c_441, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_345])).
% 5.27/1.97  tff(c_602, plain, (![A_115, B_116, C_117]: (k2_tops_2(A_115, B_116, C_117)=k2_funct_1(C_117) | ~v2_funct_1(C_117) | k2_relset_1(A_115, B_116, C_117)!=B_116 | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_2(C_117, A_115, B_116) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.27/1.97  tff(c_605, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_602])).
% 5.27/1.97  tff(c_608, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_442, c_440, c_58, c_605])).
% 5.27/1.97  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.27/1.97  tff(c_116, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_84, c_84, c_85, c_85, c_84, c_84, c_56])).
% 5.27/1.97  tff(c_117, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_116])).
% 5.27/1.97  tff(c_344, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_339, c_117])).
% 5.27/1.97  tff(c_460, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_435, c_435, c_344])).
% 5.27/1.97  tff(c_609, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_460])).
% 5.27/1.97  tff(c_352, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_339, c_52])).
% 5.27/1.97  tff(c_356, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_352])).
% 5.27/1.97  tff(c_391, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_356])).
% 5.27/1.97  tff(c_614, plain, (![C_118, B_119, A_120]: (m1_subset_1(k2_funct_1(C_118), k1_zfmisc_1(k2_zfmisc_1(B_119, A_120))) | k2_relset_1(A_120, B_119, C_118)!=B_119 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(C_118, A_120, B_119) | ~v1_funct_1(C_118))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.27/1.97  tff(c_641, plain, (![C_118, B_119, A_120]: (v1_relat_1(k2_funct_1(C_118)) | ~v1_relat_1(k2_zfmisc_1(B_119, A_120)) | k2_relset_1(A_120, B_119, C_118)!=B_119 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(C_118, A_120, B_119) | ~v1_funct_1(C_118))), inference(resolution, [status(thm)], [c_614, c_10])).
% 5.27/1.97  tff(c_653, plain, (![C_121, A_122, B_123]: (v1_relat_1(k2_funct_1(C_121)) | k2_relset_1(A_122, B_123, C_121)!=B_123 | ~v2_funct_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_2(C_121, A_122, B_123) | ~v1_funct_1(C_121))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_641])).
% 5.27/1.97  tff(c_659, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_653])).
% 5.27/1.97  tff(c_663, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_442, c_58, c_440, c_659])).
% 5.27/1.97  tff(c_30, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/1.97  tff(c_673, plain, (![C_124, B_125, A_126]: (v4_relat_1(k2_funct_1(C_124), B_125) | k2_relset_1(A_126, B_125, C_124)!=B_125 | ~v2_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2(C_124, A_126, B_125) | ~v1_funct_1(C_124))), inference(resolution, [status(thm)], [c_614, c_30])).
% 5.27/1.97  tff(c_679, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_673])).
% 5.27/1.97  tff(c_683, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_442, c_58, c_440, c_679])).
% 5.27/1.97  tff(c_42, plain, (![B_33, A_32]: (k1_relat_1(B_33)=A_32 | ~v1_partfun1(B_33, A_32) | ~v4_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.27/1.97  tff(c_686, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_683, c_42])).
% 5.27/1.97  tff(c_692, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_686])).
% 5.27/1.97  tff(c_746, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_692])).
% 5.27/1.97  tff(c_587, plain, (![C_107, A_108, B_109]: (v1_funct_1(k2_funct_1(C_107)) | k2_relset_1(A_108, B_109, C_107)!=B_109 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.27/1.97  tff(c_590, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_587])).
% 5.27/1.97  tff(c_593, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_442, c_58, c_440, c_590])).
% 5.27/1.97  tff(c_594, plain, (![C_110, B_111, A_112]: (v1_funct_2(k2_funct_1(C_110), B_111, A_112) | k2_relset_1(A_112, B_111, C_110)!=B_111 | ~v2_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))) | ~v1_funct_2(C_110, A_112, B_111) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.27/1.97  tff(c_597, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_594])).
% 5.27/1.97  tff(c_600, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_442, c_58, c_440, c_597])).
% 5.27/1.97  tff(c_36, plain, (![C_31, A_28, B_29]: (v1_partfun1(C_31, A_28) | ~v1_funct_2(C_31, A_28, B_29) | ~v1_funct_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.27/1.97  tff(c_802, plain, (![C_137, B_138, A_139]: (v1_partfun1(k2_funct_1(C_137), B_138) | ~v1_funct_2(k2_funct_1(C_137), B_138, A_139) | ~v1_funct_1(k2_funct_1(C_137)) | v1_xboole_0(A_139) | k2_relset_1(A_139, B_138, C_137)!=B_138 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_2(C_137, A_139, B_138) | ~v1_funct_1(C_137))), inference(resolution, [status(thm)], [c_614, c_36])).
% 5.27/1.97  tff(c_808, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_802])).
% 5.27/1.97  tff(c_812, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_442, c_58, c_440, c_593, c_600, c_808])).
% 5.27/1.97  tff(c_814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_746, c_812])).
% 5.27/1.97  tff(c_815, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_692])).
% 5.27/1.97  tff(c_32, plain, (![A_22, B_23, C_24]: (k1_relset_1(A_22, B_23, C_24)=k1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.27/1.97  tff(c_892, plain, (![B_147, A_148, C_149]: (k1_relset_1(B_147, A_148, k2_funct_1(C_149))=k1_relat_1(k2_funct_1(C_149)) | k2_relset_1(A_148, B_147, C_149)!=B_147 | ~v2_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))) | ~v1_funct_2(C_149, A_148, B_147) | ~v1_funct_1(C_149))), inference(resolution, [status(thm)], [c_614, c_32])).
% 5.27/1.97  tff(c_898, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_892])).
% 5.27/1.97  tff(c_902, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_442, c_58, c_440, c_815, c_898])).
% 5.27/1.97  tff(c_904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_609, c_902])).
% 5.27/1.97  tff(c_906, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_356])).
% 5.27/1.97  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.27/1.97  tff(c_913, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_906, c_2])).
% 5.27/1.97  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_913])).
% 5.27/1.97  tff(c_918, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_145])).
% 5.27/1.97  tff(c_1266, plain, (![A_192, B_193, C_194]: (k2_relset_1(A_192, B_193, C_194)=k2_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.27/1.97  tff(c_1269, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_1266])).
% 5.27/1.97  tff(c_1271, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_918, c_1269])).
% 5.27/1.97  tff(c_1272, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_98])).
% 5.27/1.97  tff(c_1287, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1272, c_52])).
% 5.27/1.97  tff(c_1291, plain, (~v1_xboole_0(k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1287])).
% 5.27/1.97  tff(c_1292, plain, (~v1_xboole_0(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_70, c_1291])).
% 5.27/1.97  tff(c_919, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_145])).
% 5.27/1.97  tff(c_937, plain, (![C_150, A_151, B_152]: (v4_relat_1(C_150, A_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/1.97  tff(c_941, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_132, c_937])).
% 5.27/1.97  tff(c_1242, plain, (![B_187, A_188]: (k1_relat_1(B_187)=A_188 | ~v1_partfun1(B_187, A_188) | ~v4_relat_1(B_187, A_188) | ~v1_relat_1(B_187))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.27/1.97  tff(c_1248, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_941, c_1242])).
% 5.27/1.97  tff(c_1254, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_919, c_1248])).
% 5.27/1.97  tff(c_1255, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1254])).
% 5.27/1.97  tff(c_1282, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1272, c_96])).
% 5.27/1.97  tff(c_1281, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1272, c_132])).
% 5.27/1.97  tff(c_1388, plain, (![C_200, A_201, B_202]: (v1_partfun1(C_200, A_201) | ~v1_funct_2(C_200, A_201, B_202) | ~v1_funct_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | v1_xboole_0(B_202))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.27/1.97  tff(c_1391, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | ~v1_funct_1('#skF_3') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1281, c_1388])).
% 5.27/1.97  tff(c_1394, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1282, c_1391])).
% 5.27/1.97  tff(c_1396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1292, c_1255, c_1394])).
% 5.27/1.97  tff(c_1397, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1254])).
% 5.27/1.97  tff(c_1403, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_132])).
% 5.27/1.97  tff(c_1455, plain, (![A_206, B_207, C_208]: (k2_relset_1(A_206, B_207, C_208)=k2_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.27/1.97  tff(c_1458, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1403, c_1455])).
% 5.27/1.97  tff(c_1460, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_918, c_1458])).
% 5.27/1.97  tff(c_1404, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_98])).
% 5.27/1.97  tff(c_1461, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_1404])).
% 5.27/1.97  tff(c_1405, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_96])).
% 5.27/1.97  tff(c_1470, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1405])).
% 5.27/1.97  tff(c_1466, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1460])).
% 5.27/1.97  tff(c_1469, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1403])).
% 5.27/1.97  tff(c_1659, plain, (![A_228, B_229, C_230]: (k2_tops_2(A_228, B_229, C_230)=k2_funct_1(C_230) | ~v2_funct_1(C_230) | k2_relset_1(A_228, B_229, C_230)!=B_229 | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_2(C_230, A_228, B_229) | ~v1_funct_1(C_230))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.27/1.97  tff(c_1662, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1469, c_1659])).
% 5.27/1.97  tff(c_1665, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1470, c_1466, c_58, c_1662])).
% 5.27/1.97  tff(c_1401, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_xboole_0, k2_tops_2(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1397, c_117])).
% 5.27/1.97  tff(c_1468, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1461, c_1461, c_1401])).
% 5.27/1.97  tff(c_1666, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1468])).
% 5.27/1.97  tff(c_1671, plain, (![C_231, B_232, A_233]: (m1_subset_1(k2_funct_1(C_231), k1_zfmisc_1(k2_zfmisc_1(B_232, A_233))) | k2_relset_1(A_233, B_232, C_231)!=B_232 | ~v2_funct_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_233, B_232))) | ~v1_funct_2(C_231, A_233, B_232) | ~v1_funct_1(C_231))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.27/1.97  tff(c_1698, plain, (![C_231, B_232, A_233]: (v1_relat_1(k2_funct_1(C_231)) | ~v1_relat_1(k2_zfmisc_1(B_232, A_233)) | k2_relset_1(A_233, B_232, C_231)!=B_232 | ~v2_funct_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_233, B_232))) | ~v1_funct_2(C_231, A_233, B_232) | ~v1_funct_1(C_231))), inference(resolution, [status(thm)], [c_1671, c_10])).
% 5.27/1.97  tff(c_1710, plain, (![C_234, A_235, B_236]: (v1_relat_1(k2_funct_1(C_234)) | k2_relset_1(A_235, B_236, C_234)!=B_236 | ~v2_funct_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~v1_funct_2(C_234, A_235, B_236) | ~v1_funct_1(C_234))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1698])).
% 5.27/1.97  tff(c_1716, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1469, c_1710])).
% 5.27/1.97  tff(c_1720, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1470, c_58, c_1466, c_1716])).
% 5.27/1.97  tff(c_1727, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1720, c_22])).
% 5.27/1.97  tff(c_1729, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1727])).
% 5.27/1.97  tff(c_20, plain, (![A_14]: (k1_relat_1(A_14)=k1_xboole_0 | k2_relat_1(A_14)!=k1_xboole_0 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.27/1.97  tff(c_1728, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0 | k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1720, c_20])).
% 5.27/1.97  tff(c_1730, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1728])).
% 5.27/1.97  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/1.97  tff(c_14, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.27/1.97  tff(c_927, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_919, c_14])).
% 5.27/1.97  tff(c_931, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_918, c_927])).
% 5.27/1.97  tff(c_1538, plain, (![B_211, A_212]: (k10_relat_1(B_211, k9_relat_1(B_211, A_212))=A_212 | ~v2_funct_1(B_211) | ~r1_tarski(A_212, k1_relat_1(B_211)) | ~v1_funct_1(B_211) | ~v1_relat_1(B_211))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.27/1.97  tff(c_1540, plain, (![A_212]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_212))=A_212 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_212, k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_919, c_1538])).
% 5.27/1.97  tff(c_1547, plain, (![A_213]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_213))=A_213 | ~r1_tarski(A_213, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_66, c_58, c_1540])).
% 5.27/1.97  tff(c_1556, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_931, c_1547])).
% 5.27/1.97  tff(c_1564, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1556])).
% 5.27/1.97  tff(c_1731, plain, (![C_237, B_238, A_239]: (v4_relat_1(k2_funct_1(C_237), B_238) | k2_relset_1(A_239, B_238, C_237)!=B_238 | ~v2_funct_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))) | ~v1_funct_2(C_237, A_239, B_238) | ~v1_funct_1(C_237))), inference(resolution, [status(thm)], [c_1671, c_30])).
% 5.27/1.97  tff(c_1737, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_xboole_0) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1469, c_1731])).
% 5.27/1.97  tff(c_1741, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1470, c_58, c_1466, c_1737])).
% 5.27/1.97  tff(c_18, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.27/1.97  tff(c_1747, plain, (k7_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1741, c_18])).
% 5.27/1.97  tff(c_1754, plain, (k7_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_1747])).
% 5.27/1.97  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.27/1.97  tff(c_1769, plain, (k9_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1754, c_16])).
% 5.27/1.97  tff(c_1773, plain, (k9_relat_1(k2_funct_1('#skF_3'), k1_xboole_0)=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_1769])).
% 5.27/1.97  tff(c_24, plain, (![B_16, A_15]: (k9_relat_1(k2_funct_1(B_16), A_15)=k10_relat_1(B_16, A_15) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.27/1.97  tff(c_1778, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1773, c_24])).
% 5.27/1.97  tff(c_1785, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_138, c_66, c_58, c_1564, c_1778])).
% 5.27/1.97  tff(c_1787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1730, c_1785])).
% 5.27/1.97  tff(c_1788, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1728])).
% 5.27/1.97  tff(c_1799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1729, c_1788])).
% 5.27/1.97  tff(c_1801, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1727])).
% 5.27/1.97  tff(c_1903, plain, (![B_249, A_250, C_251]: (k1_relset_1(B_249, A_250, k2_funct_1(C_251))=k1_relat_1(k2_funct_1(C_251)) | k2_relset_1(A_250, B_249, C_251)!=B_249 | ~v2_funct_1(C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))) | ~v1_funct_2(C_251, A_250, B_249) | ~v1_funct_1(C_251))), inference(resolution, [status(thm)], [c_1671, c_32])).
% 5.27/1.97  tff(c_1909, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1469, c_1903])).
% 5.27/1.97  tff(c_1913, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1470, c_58, c_1466, c_1801, c_1909])).
% 5.27/1.97  tff(c_1915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1666, c_1913])).
% 5.27/1.97  tff(c_1916, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_116])).
% 5.27/1.97  tff(c_2121, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_2115, c_2115, c_1916])).
% 5.27/1.97  tff(c_2320, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_2234, c_2121])).
% 5.27/1.97  tff(c_2414, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2413, c_2320])).
% 5.27/1.97  tff(c_1962, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1959, c_18])).
% 5.27/1.97  tff(c_1965, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1962])).
% 5.27/1.97  tff(c_1974, plain, (![B_262, A_263]: (k2_relat_1(k7_relat_1(B_262, A_263))=k9_relat_1(B_262, A_263) | ~v1_relat_1(B_262))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.27/1.97  tff(c_1983, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1965, c_1974])).
% 5.27/1.97  tff(c_1987, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1983])).
% 5.27/1.97  tff(c_2117, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_1987])).
% 5.27/1.97  tff(c_2315, plain, (![B_294, A_295]: (k10_relat_1(B_294, k9_relat_1(B_294, A_295))=A_295 | ~v2_funct_1(B_294) | ~r1_tarski(A_295, k1_relat_1(B_294)) | ~v1_funct_1(B_294) | ~v1_relat_1(B_294))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.27/1.97  tff(c_2321, plain, (![B_296]: (k10_relat_1(B_296, k9_relat_1(B_296, k1_relat_1(B_296)))=k1_relat_1(B_296) | ~v2_funct_1(B_296) | ~v1_funct_1(B_296) | ~v1_relat_1(B_296))), inference(resolution, [status(thm)], [c_8, c_2315])).
% 5.27/1.97  tff(c_2334, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2117, c_2321])).
% 5.27/1.97  tff(c_2341, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_66, c_58, c_2334])).
% 5.27/1.97  tff(c_2424, plain, (![C_313, B_314, A_315]: (m1_subset_1(k2_funct_1(C_313), k1_zfmisc_1(k2_zfmisc_1(B_314, A_315))) | k2_relset_1(A_315, B_314, C_313)!=B_314 | ~v2_funct_1(C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_315, B_314))) | ~v1_funct_2(C_313, A_315, B_314) | ~v1_funct_1(C_313))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.27/1.97  tff(c_2451, plain, (![C_313, B_314, A_315]: (v1_relat_1(k2_funct_1(C_313)) | ~v1_relat_1(k2_zfmisc_1(B_314, A_315)) | k2_relset_1(A_315, B_314, C_313)!=B_314 | ~v2_funct_1(C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_315, B_314))) | ~v1_funct_2(C_313, A_315, B_314) | ~v1_funct_1(C_313))), inference(resolution, [status(thm)], [c_2424, c_10])).
% 5.27/1.97  tff(c_2463, plain, (![C_316, A_317, B_318]: (v1_relat_1(k2_funct_1(C_316)) | k2_relset_1(A_317, B_318, C_316)!=B_318 | ~v2_funct_1(C_316) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))) | ~v1_funct_2(C_316, A_317, B_318) | ~v1_funct_1(C_316))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2451])).
% 5.27/1.97  tff(c_2469, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2241, c_2463])).
% 5.27/1.97  tff(c_2473, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2242, c_58, c_2239, c_2469])).
% 5.27/1.97  tff(c_2482, plain, (![C_319, B_320, A_321]: (v4_relat_1(k2_funct_1(C_319), B_320) | k2_relset_1(A_321, B_320, C_319)!=B_320 | ~v2_funct_1(C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_321, B_320))) | ~v1_funct_2(C_319, A_321, B_320) | ~v1_funct_1(C_319))), inference(resolution, [status(thm)], [c_2424, c_30])).
% 5.27/1.97  tff(c_2488, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2241, c_2482])).
% 5.27/1.97  tff(c_2492, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2242, c_58, c_2239, c_2488])).
% 5.27/1.97  tff(c_2498, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2492, c_18])).
% 5.27/1.97  tff(c_2504, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_2498])).
% 5.27/1.97  tff(c_2508, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2504, c_16])).
% 5.27/1.97  tff(c_2512, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_2508])).
% 5.27/1.97  tff(c_2519, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2512, c_24])).
% 5.27/1.97  tff(c_2526, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_66, c_58, c_2341, c_2519])).
% 5.27/1.97  tff(c_2627, plain, (![B_329, A_330, C_331]: (k2_relset_1(B_329, A_330, k2_funct_1(C_331))=k2_relat_1(k2_funct_1(C_331)) | k2_relset_1(A_330, B_329, C_331)!=B_329 | ~v2_funct_1(C_331) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_330, B_329))) | ~v1_funct_2(C_331, A_330, B_329) | ~v1_funct_1(C_331))), inference(resolution, [status(thm)], [c_2424, c_34])).
% 5.27/1.97  tff(c_2633, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2241, c_2627])).
% 5.27/1.97  tff(c_2637, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2242, c_58, c_2239, c_2526, c_2633])).
% 5.27/1.97  tff(c_2639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2414, c_2637])).
% 5.27/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/1.97  
% 5.27/1.97  Inference rules
% 5.27/1.97  ----------------------
% 5.27/1.97  #Ref     : 0
% 5.27/1.97  #Sup     : 585
% 5.27/1.97  #Fact    : 0
% 5.27/1.97  #Define  : 0
% 5.27/1.97  #Split   : 24
% 5.27/1.97  #Chain   : 0
% 5.27/1.97  #Close   : 0
% 5.27/1.97  
% 5.27/1.97  Ordering : KBO
% 5.27/1.97  
% 5.27/1.97  Simplification rules
% 5.27/1.97  ----------------------
% 5.27/1.97  #Subsume      : 19
% 5.27/1.97  #Demod        : 668
% 5.27/1.97  #Tautology    : 367
% 5.27/1.97  #SimpNegUnit  : 27
% 5.27/1.97  #BackRed      : 97
% 5.27/1.97  
% 5.27/1.97  #Partial instantiations: 0
% 5.27/1.97  #Strategies tried      : 1
% 5.27/1.97  
% 5.27/1.97  Timing (in seconds)
% 5.27/1.97  ----------------------
% 5.27/1.98  Preprocessing        : 0.37
% 5.27/1.98  Parsing              : 0.20
% 5.27/1.98  CNF conversion       : 0.03
% 5.27/1.98  Main loop            : 0.77
% 5.27/1.98  Inferencing          : 0.28
% 5.27/1.98  Reduction            : 0.26
% 5.27/1.98  Demodulation         : 0.18
% 5.27/1.98  BG Simplification    : 0.04
% 5.27/1.98  Subsumption          : 0.12
% 5.27/1.98  Abstraction          : 0.04
% 5.27/1.98  MUC search           : 0.00
% 5.27/1.98  Cooper               : 0.00
% 5.27/1.98  Total                : 1.23
% 5.27/1.98  Index Insertion      : 0.00
% 5.27/1.98  Index Deletion       : 0.00
% 5.27/1.98  Index Matching       : 0.00
% 5.27/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
