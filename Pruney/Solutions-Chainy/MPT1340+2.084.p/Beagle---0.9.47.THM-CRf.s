%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:42 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :  230 (44136 expanded)
%              Number of leaves         :   45 (15475 expanded)
%              Depth                    :   25
%              Number of atoms          :  522 (128579 expanded)
%              Number of equality atoms :  112 (29648 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_209,negated_conjecture,(
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

tff(f_163,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_92,axiom,(
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

tff(f_116,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_159,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_149,axiom,(
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

tff(f_175,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_187,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_88,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_96,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_88])).

tff(c_82,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_95,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_88])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_112,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_95,c_76])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_124,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_112,c_124])).

tff(c_179,plain,(
    ! [B_60,A_61] :
      ( k1_relat_1(B_60) = A_61
      | ~ v1_partfun1(B_60,A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_182,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_179])).

tff(c_185,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_182])).

tff(c_186,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_245,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_253,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_245])).

tff(c_74,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_107,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_95,c_74])).

tff(c_254,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_107])).

tff(c_78,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_105,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_95,c_78])).

tff(c_263,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_105])).

tff(c_262,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_112])).

tff(c_317,plain,(
    ! [B_80,C_81,A_82] :
      ( k1_xboole_0 = B_80
      | v1_partfun1(C_81,A_82)
      | ~ v1_funct_2(C_81,A_82,B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_80)))
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_320,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_262,c_317])).

tff(c_326,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_263,c_320])).

tff(c_327,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_326])).

tff(c_332,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_263])).

tff(c_331,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_262])).

tff(c_26,plain,(
    ! [C_17,A_15] :
      ( k1_xboole_0 = C_17
      | ~ v1_funct_2(C_17,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_382,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_331,c_26])).

tff(c_405,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_382])).

tff(c_415,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_418,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_186])).

tff(c_417,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_332])).

tff(c_416,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_331])).

tff(c_44,plain,(
    ! [C_26,B_25] :
      ( v1_partfun1(C_26,k1_xboole_0)
      | ~ v1_funct_2(C_26,k1_xboole_0,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25)))
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_468,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_416,c_44])).

tff(c_502,plain,(
    v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_417,c_468])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_502])).

tff(c_505,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_509,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_332])).

tff(c_507,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_331])).

tff(c_665,plain,(
    ! [A_95,B_96,D_97] :
      ( r2_funct_2(A_95,B_96,D_97,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(D_97,A_95,B_96)
      | ~ v1_funct_1(D_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_667,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_665])).

tff(c_674,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_509,c_667])).

tff(c_506,plain,(
    k2_struct_0('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_525,plain,(
    k2_struct_0('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_506])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_514,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_327])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_202,plain,(
    ! [A_63] :
      ( m1_subset_1(A_63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_63),k2_relat_1(A_63))))
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_20,plain,(
    ! [C_11,A_9,B_10] :
      ( v4_relat_1(C_11,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_223,plain,(
    ! [A_64] :
      ( v4_relat_1(A_64,k1_relat_1(A_64))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_202,c_20])).

tff(c_829,plain,(
    ! [A_119] :
      ( v4_relat_1(k2_funct_1(A_119),k2_relat_1(A_119))
      | ~ v1_funct_1(k2_funct_1(A_119))
      | ~ v1_relat_1(k2_funct_1(A_119))
      | ~ v2_funct_1(A_119)
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_223])).

tff(c_835,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_829])).

tff(c_844,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80,c_72,c_835])).

tff(c_845,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_844])).

tff(c_869,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_845])).

tff(c_873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80,c_72,c_869])).

tff(c_874,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v4_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_844])).

tff(c_876,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_879,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_876])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80,c_72,c_879])).

tff(c_885,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_259,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_253])).

tff(c_330,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_327,c_259])).

tff(c_566,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_330])).

tff(c_1212,plain,(
    ! [C_131,B_132,A_133] :
      ( v1_funct_2(k2_funct_1(C_131),B_132,A_133)
      | k2_relset_1(A_133,B_132,C_131) != B_132
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(C_131,A_133,B_132)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1224,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_1212])).

tff(c_1240,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_509,c_72,c_566,c_1224])).

tff(c_1259,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_tops_2(A_134,B_135,C_136) = k2_funct_1(C_136)
      | ~ v2_funct_1(C_136)
      | k2_relset_1(A_134,B_135,C_136) != B_135
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_2(C_136,A_134,B_135)
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1271,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_1259])).

tff(c_1287,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_509,c_566,c_72,c_1271])).

tff(c_64,plain,(
    ! [A_35,B_36,C_37] :
      ( m1_subset_1(k2_tops_2(A_35,B_36,C_37),k1_zfmisc_1(k2_zfmisc_1(B_36,A_35)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1302,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3')))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1287,c_64])).

tff(c_1306,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_509,c_507,c_1302])).

tff(c_66,plain,(
    ! [A_35,B_36,C_37] :
      ( v1_funct_2(k2_tops_2(A_35,B_36,C_37),B_36,A_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1345,plain,
    ( v1_funct_2(k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1306,c_66])).

tff(c_1388,plain,(
    v1_funct_2(k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_1240,c_1345])).

tff(c_723,plain,(
    ! [A_108,B_109,C_110] :
      ( m1_subset_1(k2_tops_2(A_108,B_109,C_110),k1_zfmisc_1(k2_zfmisc_1(B_109,A_108)))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(C_110,A_108,B_109)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_519,plain,(
    ! [C_17,A_15] :
      ( C_17 = '#skF_3'
      | ~ v1_funct_2(C_17,A_15,'#skF_3')
      | A_15 = '#skF_3'
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_505,c_505,c_26])).

tff(c_4627,plain,(
    ! [B_214,C_215] :
      ( k2_tops_2('#skF_3',B_214,C_215) = '#skF_3'
      | ~ v1_funct_2(k2_tops_2('#skF_3',B_214,C_215),B_214,'#skF_3')
      | B_214 = '#skF_3'
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_214)))
      | ~ v1_funct_2(C_215,'#skF_3',B_214)
      | ~ v1_funct_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_723,c_519])).

tff(c_4636,plain,
    ( k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_struct_0('#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1388,c_4627])).

tff(c_4646,plain,
    ( k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_1240,c_1306,c_4636])).

tff(c_4647,plain,(
    k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_4646])).

tff(c_70,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_130,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_96,c_96,c_95,c_95,c_95,c_70])).

tff(c_260,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_254,c_254,c_130])).

tff(c_329,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_327,c_327,c_260])).

tff(c_564,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3',k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_505,c_329])).

tff(c_1295,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3',k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_564])).

tff(c_4656,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4647,c_1295])).

tff(c_4666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_4656])).

tff(c_4667,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_4671,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_112])).

tff(c_4732,plain,(
    ! [A_217,B_218,C_219] :
      ( k2_relset_1(A_217,B_218,C_219) = k2_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4736,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4671,c_4732])).

tff(c_4672,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_107])).

tff(c_4737,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4736,c_4672])).

tff(c_4673,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_105])).

tff(c_4744,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4737,c_4673])).

tff(c_4743,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4737,c_4671])).

tff(c_4886,plain,(
    ! [A_240,B_241,D_242] :
      ( r2_funct_2(A_240,B_241,D_242,D_242)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_2(D_242,A_240,B_241)
      | ~ v1_funct_1(D_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4890,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_4886])).

tff(c_4894,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_4890])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4742,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4737,c_4736])).

tff(c_5539,plain,(
    ! [A_293,B_294,C_295] :
      ( k2_tops_2(A_293,B_294,C_295) = k2_funct_1(C_295)
      | ~ v2_funct_1(C_295)
      | k2_relset_1(A_293,B_294,C_295) != B_294
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ v1_funct_2(C_295,A_293,B_294)
      | ~ v1_funct_1(C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_5551,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_5539])).

tff(c_5559,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_4742,c_72,c_5551])).

tff(c_5589,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5559,c_64])).

tff(c_5602,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_4743,c_5589])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5868,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5602,c_22])).

tff(c_5076,plain,(
    ! [C_268,A_269,B_270] :
      ( v1_funct_1(k2_funct_1(C_268))
      | k2_relset_1(A_269,B_270,C_268) != B_270
      | ~ v2_funct_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_2(C_268,A_269,B_270)
      | ~ v1_funct_1(C_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5085,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_5076])).

tff(c_5090,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_72,c_4742,c_5085])).

tff(c_5474,plain,(
    ! [C_288,B_289,A_290] :
      ( v1_funct_2(k2_funct_1(C_288),B_289,A_290)
      | k2_relset_1(A_290,B_289,C_288) != B_289
      | ~ v2_funct_1(C_288)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289)))
      | ~ v1_funct_2(C_288,A_290,B_289)
      | ~ v1_funct_1(C_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5486,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_5474])).

tff(c_5494,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_72,c_4742,c_5486])).

tff(c_52,plain,(
    ! [C_29,A_27,B_28] :
      ( v1_funct_1(k2_funct_1(C_29))
      | k2_relset_1(A_27,B_28,C_29) != B_28
      | ~ v2_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5799,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5602,c_52])).

tff(c_5844,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5090,c_5494,c_5799])).

tff(c_6116,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5868,c_5844])).

tff(c_6117,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6116])).

tff(c_6120,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_6117])).

tff(c_6124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80,c_72,c_6120])).

tff(c_6125,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6116])).

tff(c_6127,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6125])).

tff(c_6130,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6127])).

tff(c_6134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80,c_72,c_6130])).

tff(c_6136,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6125])).

tff(c_4975,plain,(
    ! [A_258,B_259,C_260] :
      ( m1_subset_1(k2_tops_2(A_258,B_259,C_260),k1_zfmisc_1(k2_zfmisc_1(B_259,A_258)))
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_260,A_258,B_259)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_5019,plain,(
    ! [A_258,B_259,C_260] :
      ( v1_relat_1(k2_tops_2(A_258,B_259,C_260))
      | ~ v1_relat_1(k2_zfmisc_1(B_259,A_258))
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_260,A_258,B_259)
      | ~ v1_funct_1(C_260) ) ),
    inference(resolution,[status(thm)],[c_4975,c_2])).

tff(c_5036,plain,(
    ! [A_261,B_262,C_263] :
      ( v1_relat_1(k2_tops_2(A_261,B_262,C_263))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2(C_263,A_261,B_262)
      | ~ v1_funct_1(C_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_5019])).

tff(c_5045,plain,
    ( v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_5036])).

tff(c_5050,plain,(
    v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_5045])).

tff(c_4875,plain,(
    ! [A_237,B_238,C_239] :
      ( v1_funct_1(k2_tops_2(A_237,B_238,C_239))
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_2(C_239,A_237,B_238)
      | ~ v1_funct_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_4881,plain,
    ( v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_4875])).

tff(c_4885,plain,(
    v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_4881])).

tff(c_5182,plain,(
    ! [A_282,B_283,C_284] :
      ( k2_tops_2(A_282,B_283,C_284) = k2_funct_1(C_284)
      | ~ v2_funct_1(C_284)
      | k2_relset_1(A_282,B_283,C_284) != B_283
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_2(C_284,A_282,B_283)
      | ~ v1_funct_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_5191,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_5182])).

tff(c_5196,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_4742,c_72,c_5191])).

tff(c_5200,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5196,c_5050])).

tff(c_4782,plain,(
    ! [A_221] :
      ( m1_subset_1(A_221,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_221),k2_relat_1(A_221))))
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4807,plain,(
    ! [A_222] :
      ( v4_relat_1(A_222,k1_relat_1(A_222))
      | ~ v1_funct_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_4782,c_20])).

tff(c_36,plain,(
    ! [B_19] :
      ( v1_partfun1(B_19,k1_relat_1(B_19))
      | ~ v4_relat_1(B_19,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4825,plain,(
    ! [A_226] :
      ( v1_partfun1(A_226,k1_relat_1(A_226))
      | ~ v1_funct_1(A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(resolution,[status(thm)],[c_4807,c_36])).

tff(c_4828,plain,(
    ! [A_7] :
      ( v1_partfun1(k2_funct_1(A_7),k2_relat_1(A_7))
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4825])).

tff(c_5058,plain,(
    ! [A_265,B_266,C_267] :
      ( v4_relat_1(k2_tops_2(A_265,B_266,C_267),B_266)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_2(C_267,A_265,B_266)
      | ~ v1_funct_1(C_267) ) ),
    inference(resolution,[status(thm)],[c_4975,c_20])).

tff(c_5064,plain,
    ( v4_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4743,c_5058])).

tff(c_5069,plain,(
    v4_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4744,c_5064])).

tff(c_38,plain,(
    ! [B_19,A_18] :
      ( k1_relat_1(B_19) = A_18
      | ~ v1_partfun1(B_19,A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5072,plain,
    ( k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_5069,c_38])).

tff(c_5075,plain,
    ( k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5050,c_5072])).

tff(c_5103,plain,(
    ~ v1_partfun1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5075])).

tff(c_5197,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5196,c_5103])).

tff(c_5337,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4828,c_5197])).

tff(c_5341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80,c_72,c_5200,c_5090,c_5337])).

tff(c_5342,plain,(
    k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5075])).

tff(c_4801,plain,(
    ! [A_221] :
      ( k2_relset_1(k1_relat_1(A_221),k2_relat_1(A_221),A_221) = k2_relat_1(A_221)
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(resolution,[status(thm)],[c_4782,c_22])).

tff(c_5359,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5342,c_4801])).

tff(c_5386,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5050,c_4885,c_5359])).

tff(c_5562,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5559,c_5559,c_5559,c_5386])).

tff(c_6144,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6136,c_6136,c_5562])).

tff(c_6126,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6116])).

tff(c_62,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_tops_2(A_32,B_33,C_34) = k2_funct_1(C_34)
      | ~ v2_funct_1(C_34)
      | k2_relset_1(A_32,B_33,C_34) != B_33
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_5791,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5602,c_62])).

tff(c_5835,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5090,c_5494,c_5791])).

tff(c_6432,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6144,c_6126,c_5835])).

tff(c_4669,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_4667,c_4667,c_130])).

tff(c_4756,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4737,c_4737,c_4737,c_4669])).

tff(c_5574,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5559,c_4756])).

tff(c_6438,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6432,c_5574])).

tff(c_6459,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6438])).

tff(c_6462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80,c_72,c_4894,c_6459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.42  
% 7.01/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.42  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.01/2.42  
% 7.01/2.42  %Foreground sorts:
% 7.01/2.42  
% 7.01/2.42  
% 7.01/2.42  %Background operators:
% 7.01/2.42  
% 7.01/2.42  
% 7.01/2.42  %Foreground operators:
% 7.01/2.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.01/2.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.01/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.01/2.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.01/2.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.01/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.01/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.01/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.01/2.42  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 7.01/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.01/2.42  tff('#skF_2', type, '#skF_2': $i).
% 7.01/2.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.01/2.42  tff('#skF_3', type, '#skF_3': $i).
% 7.01/2.42  tff('#skF_1', type, '#skF_1': $i).
% 7.01/2.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.01/2.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.01/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.01/2.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.01/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.01/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.01/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.01/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.01/2.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.01/2.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.01/2.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.01/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.01/2.42  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.01/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.01/2.42  
% 7.01/2.45  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.01/2.45  tff(f_209, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 7.01/2.45  tff(f_163, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.01/2.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.01/2.45  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.01/2.45  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 7.01/2.45  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.01/2.45  tff(f_133, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 7.01/2.45  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.01/2.45  tff(f_116, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.01/2.45  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 7.01/2.45  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.01/2.45  tff(f_159, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.01/2.45  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.01/2.45  tff(f_175, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 7.01/2.45  tff(f_187, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 7.01/2.45  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 7.01/2.45  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.01/2.45  tff(c_86, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_88, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.01/2.45  tff(c_96, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_88])).
% 7.01/2.45  tff(c_82, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_95, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_88])).
% 7.01/2.45  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_112, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_95, c_76])).
% 7.01/2.45  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.01/2.45  tff(c_115, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_112, c_2])).
% 7.01/2.45  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_115])).
% 7.01/2.45  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_124, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.01/2.45  tff(c_128, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_112, c_124])).
% 7.01/2.45  tff(c_179, plain, (![B_60, A_61]: (k1_relat_1(B_60)=A_61 | ~v1_partfun1(B_60, A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.01/2.45  tff(c_182, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_179])).
% 7.01/2.45  tff(c_185, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_182])).
% 7.01/2.45  tff(c_186, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_185])).
% 7.01/2.45  tff(c_245, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.01/2.45  tff(c_253, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_245])).
% 7.01/2.45  tff(c_74, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_107, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_95, c_74])).
% 7.01/2.45  tff(c_254, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_107])).
% 7.01/2.45  tff(c_78, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_105, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_95, c_78])).
% 7.01/2.45  tff(c_263, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_105])).
% 7.01/2.45  tff(c_262, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_112])).
% 7.01/2.45  tff(c_317, plain, (![B_80, C_81, A_82]: (k1_xboole_0=B_80 | v1_partfun1(C_81, A_82) | ~v1_funct_2(C_81, A_82, B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_80))) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.01/2.45  tff(c_320, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_262, c_317])).
% 7.01/2.45  tff(c_326, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_263, c_320])).
% 7.01/2.45  tff(c_327, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_186, c_326])).
% 7.01/2.45  tff(c_332, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_263])).
% 7.01/2.45  tff(c_331, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_262])).
% 7.01/2.45  tff(c_26, plain, (![C_17, A_15]: (k1_xboole_0=C_17 | ~v1_funct_2(C_17, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.01/2.45  tff(c_382, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_331, c_26])).
% 7.01/2.45  tff(c_405, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_332, c_382])).
% 7.01/2.45  tff(c_415, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_405])).
% 7.01/2.45  tff(c_418, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_415, c_186])).
% 7.01/2.45  tff(c_417, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_415, c_332])).
% 7.01/2.45  tff(c_416, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_331])).
% 7.01/2.45  tff(c_44, plain, (![C_26, B_25]: (v1_partfun1(C_26, k1_xboole_0) | ~v1_funct_2(C_26, k1_xboole_0, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.01/2.45  tff(c_468, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_416, c_44])).
% 7.01/2.45  tff(c_502, plain, (v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_417, c_468])).
% 7.01/2.45  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_418, c_502])).
% 7.01/2.45  tff(c_505, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_405])).
% 7.01/2.45  tff(c_509, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_332])).
% 7.01/2.45  tff(c_507, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_331])).
% 7.01/2.45  tff(c_665, plain, (![A_95, B_96, D_97]: (r2_funct_2(A_95, B_96, D_97, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(D_97, A_95, B_96) | ~v1_funct_1(D_97))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.01/2.45  tff(c_667, plain, (r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_507, c_665])).
% 7.01/2.45  tff(c_674, plain, (r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_509, c_667])).
% 7.01/2.45  tff(c_506, plain, (k2_struct_0('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_405])).
% 7.01/2.45  tff(c_525, plain, (k2_struct_0('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_506])).
% 7.01/2.45  tff(c_8, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.01/2.45  tff(c_10, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.01/2.45  tff(c_514, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_327])).
% 7.01/2.45  tff(c_14, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.01/2.45  tff(c_202, plain, (![A_63]: (m1_subset_1(A_63, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_63), k2_relat_1(A_63)))) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.01/2.45  tff(c_20, plain, (![C_11, A_9, B_10]: (v4_relat_1(C_11, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.01/2.45  tff(c_223, plain, (![A_64]: (v4_relat_1(A_64, k1_relat_1(A_64)) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_202, c_20])).
% 7.01/2.45  tff(c_829, plain, (![A_119]: (v4_relat_1(k2_funct_1(A_119), k2_relat_1(A_119)) | ~v1_funct_1(k2_funct_1(A_119)) | ~v1_relat_1(k2_funct_1(A_119)) | ~v2_funct_1(A_119) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_14, c_223])).
% 7.01/2.45  tff(c_835, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_514, c_829])).
% 7.01/2.45  tff(c_844, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_80, c_72, c_835])).
% 7.01/2.45  tff(c_845, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_844])).
% 7.01/2.45  tff(c_869, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_845])).
% 7.01/2.45  tff(c_873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_80, c_72, c_869])).
% 7.01/2.45  tff(c_874, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | v4_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_844])).
% 7.01/2.45  tff(c_876, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_874])).
% 7.01/2.45  tff(c_879, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_876])).
% 7.01/2.45  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_80, c_72, c_879])).
% 7.01/2.45  tff(c_885, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_874])).
% 7.01/2.45  tff(c_259, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_253])).
% 7.01/2.45  tff(c_330, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_327, c_327, c_259])).
% 7.01/2.45  tff(c_566, plain, (k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_330])).
% 7.01/2.45  tff(c_1212, plain, (![C_131, B_132, A_133]: (v1_funct_2(k2_funct_1(C_131), B_132, A_133) | k2_relset_1(A_133, B_132, C_131)!=B_132 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(C_131, A_133, B_132) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.01/2.45  tff(c_1224, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_507, c_1212])).
% 7.01/2.45  tff(c_1240, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_509, c_72, c_566, c_1224])).
% 7.01/2.45  tff(c_1259, plain, (![A_134, B_135, C_136]: (k2_tops_2(A_134, B_135, C_136)=k2_funct_1(C_136) | ~v2_funct_1(C_136) | k2_relset_1(A_134, B_135, C_136)!=B_135 | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_2(C_136, A_134, B_135) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.01/2.45  tff(c_1271, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_507, c_1259])).
% 7.01/2.45  tff(c_1287, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_509, c_566, c_72, c_1271])).
% 7.01/2.45  tff(c_64, plain, (![A_35, B_36, C_37]: (m1_subset_1(k2_tops_2(A_35, B_36, C_37), k1_zfmisc_1(k2_zfmisc_1(B_36, A_35))) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(C_37, A_35, B_36) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.01/2.45  tff(c_1302, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3'))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1287, c_64])).
% 7.01/2.45  tff(c_1306, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_509, c_507, c_1302])).
% 7.01/2.45  tff(c_66, plain, (![A_35, B_36, C_37]: (v1_funct_2(k2_tops_2(A_35, B_36, C_37), B_36, A_35) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(C_37, A_35, B_36) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.01/2.45  tff(c_1345, plain, (v1_funct_2(k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1306, c_66])).
% 7.01/2.45  tff(c_1388, plain, (v1_funct_2(k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_885, c_1240, c_1345])).
% 7.01/2.45  tff(c_723, plain, (![A_108, B_109, C_110]: (m1_subset_1(k2_tops_2(A_108, B_109, C_110), k1_zfmisc_1(k2_zfmisc_1(B_109, A_108))) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(C_110, A_108, B_109) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.01/2.45  tff(c_519, plain, (![C_17, A_15]: (C_17='#skF_3' | ~v1_funct_2(C_17, A_15, '#skF_3') | A_15='#skF_3' | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_505, c_505, c_26])).
% 7.01/2.45  tff(c_4627, plain, (![B_214, C_215]: (k2_tops_2('#skF_3', B_214, C_215)='#skF_3' | ~v1_funct_2(k2_tops_2('#skF_3', B_214, C_215), B_214, '#skF_3') | B_214='#skF_3' | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_214))) | ~v1_funct_2(C_215, '#skF_3', B_214) | ~v1_funct_1(C_215))), inference(resolution, [status(thm)], [c_723, c_519])).
% 7.01/2.45  tff(c_4636, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | k2_struct_0('#skF_1')='#skF_3' | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1388, c_4627])).
% 7.01/2.45  tff(c_4646, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_885, c_1240, c_1306, c_4636])).
% 7.01/2.45  tff(c_4647, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_525, c_4646])).
% 7.01/2.45  tff(c_70, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.01/2.45  tff(c_130, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_96, c_96, c_95, c_95, c_95, c_70])).
% 7.01/2.45  tff(c_260, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_254, c_254, c_130])).
% 7.01/2.45  tff(c_329, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k1_xboole_0, k2_tops_2(k1_xboole_0, k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_327, c_327, c_260])).
% 7.01/2.45  tff(c_564, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_505, c_329])).
% 7.01/2.45  tff(c_1295, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1287, c_564])).
% 7.01/2.45  tff(c_4656, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4647, c_1295])).
% 7.01/2.45  tff(c_4666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_674, c_4656])).
% 7.01/2.45  tff(c_4667, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_185])).
% 7.01/2.45  tff(c_4671, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_112])).
% 7.01/2.45  tff(c_4732, plain, (![A_217, B_218, C_219]: (k2_relset_1(A_217, B_218, C_219)=k2_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.01/2.45  tff(c_4736, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4671, c_4732])).
% 7.01/2.45  tff(c_4672, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_107])).
% 7.01/2.45  tff(c_4737, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4736, c_4672])).
% 7.01/2.45  tff(c_4673, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_105])).
% 7.01/2.45  tff(c_4744, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4737, c_4673])).
% 7.01/2.45  tff(c_4743, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_4737, c_4671])).
% 7.01/2.45  tff(c_4886, plain, (![A_240, B_241, D_242]: (r2_funct_2(A_240, B_241, D_242, D_242) | ~m1_subset_1(D_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_2(D_242, A_240, B_241) | ~v1_funct_1(D_242))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.01/2.45  tff(c_4890, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_4886])).
% 7.01/2.45  tff(c_4894, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_4890])).
% 7.01/2.45  tff(c_16, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.01/2.45  tff(c_12, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.01/2.45  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.01/2.45  tff(c_4742, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4737, c_4736])).
% 7.01/2.45  tff(c_5539, plain, (![A_293, B_294, C_295]: (k2_tops_2(A_293, B_294, C_295)=k2_funct_1(C_295) | ~v2_funct_1(C_295) | k2_relset_1(A_293, B_294, C_295)!=B_294 | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~v1_funct_2(C_295, A_293, B_294) | ~v1_funct_1(C_295))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.01/2.45  tff(c_5551, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_5539])).
% 7.01/2.45  tff(c_5559, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_4742, c_72, c_5551])).
% 7.01/2.45  tff(c_5589, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5559, c_64])).
% 7.01/2.45  tff(c_5602, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_4743, c_5589])).
% 7.01/2.45  tff(c_22, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.01/2.45  tff(c_5868, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5602, c_22])).
% 7.01/2.45  tff(c_5076, plain, (![C_268, A_269, B_270]: (v1_funct_1(k2_funct_1(C_268)) | k2_relset_1(A_269, B_270, C_268)!=B_270 | ~v2_funct_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_2(C_268, A_269, B_270) | ~v1_funct_1(C_268))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.01/2.45  tff(c_5085, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_5076])).
% 7.01/2.45  tff(c_5090, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_72, c_4742, c_5085])).
% 7.01/2.45  tff(c_5474, plain, (![C_288, B_289, A_290]: (v1_funct_2(k2_funct_1(C_288), B_289, A_290) | k2_relset_1(A_290, B_289, C_288)!=B_289 | ~v2_funct_1(C_288) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))) | ~v1_funct_2(C_288, A_290, B_289) | ~v1_funct_1(C_288))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.01/2.45  tff(c_5486, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_5474])).
% 7.01/2.45  tff(c_5494, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_72, c_4742, c_5486])).
% 7.01/2.45  tff(c_52, plain, (![C_29, A_27, B_28]: (v1_funct_1(k2_funct_1(C_29)) | k2_relset_1(A_27, B_28, C_29)!=B_28 | ~v2_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.01/2.45  tff(c_5799, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5602, c_52])).
% 7.01/2.45  tff(c_5844, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5090, c_5494, c_5799])).
% 7.01/2.45  tff(c_6116, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5868, c_5844])).
% 7.01/2.45  tff(c_6117, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6116])).
% 7.01/2.45  tff(c_6120, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_6117])).
% 7.01/2.45  tff(c_6124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_80, c_72, c_6120])).
% 7.01/2.45  tff(c_6125, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_6116])).
% 7.01/2.45  tff(c_6127, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_6125])).
% 7.01/2.45  tff(c_6130, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_6127])).
% 7.01/2.45  tff(c_6134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_80, c_72, c_6130])).
% 7.01/2.45  tff(c_6136, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_6125])).
% 7.01/2.45  tff(c_4975, plain, (![A_258, B_259, C_260]: (m1_subset_1(k2_tops_2(A_258, B_259, C_260), k1_zfmisc_1(k2_zfmisc_1(B_259, A_258))) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(C_260, A_258, B_259) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.01/2.45  tff(c_5019, plain, (![A_258, B_259, C_260]: (v1_relat_1(k2_tops_2(A_258, B_259, C_260)) | ~v1_relat_1(k2_zfmisc_1(B_259, A_258)) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(C_260, A_258, B_259) | ~v1_funct_1(C_260))), inference(resolution, [status(thm)], [c_4975, c_2])).
% 7.01/2.45  tff(c_5036, plain, (![A_261, B_262, C_263]: (v1_relat_1(k2_tops_2(A_261, B_262, C_263)) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2(C_263, A_261, B_262) | ~v1_funct_1(C_263))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_5019])).
% 7.01/2.45  tff(c_5045, plain, (v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_5036])).
% 7.01/2.45  tff(c_5050, plain, (v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_5045])).
% 7.01/2.45  tff(c_4875, plain, (![A_237, B_238, C_239]: (v1_funct_1(k2_tops_2(A_237, B_238, C_239)) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_2(C_239, A_237, B_238) | ~v1_funct_1(C_239))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.01/2.45  tff(c_4881, plain, (v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_4875])).
% 7.01/2.45  tff(c_4885, plain, (v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_4881])).
% 7.01/2.45  tff(c_5182, plain, (![A_282, B_283, C_284]: (k2_tops_2(A_282, B_283, C_284)=k2_funct_1(C_284) | ~v2_funct_1(C_284) | k2_relset_1(A_282, B_283, C_284)!=B_283 | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_2(C_284, A_282, B_283) | ~v1_funct_1(C_284))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.01/2.45  tff(c_5191, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_5182])).
% 7.01/2.45  tff(c_5196, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_4742, c_72, c_5191])).
% 7.01/2.45  tff(c_5200, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5196, c_5050])).
% 7.01/2.45  tff(c_4782, plain, (![A_221]: (m1_subset_1(A_221, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_221), k2_relat_1(A_221)))) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.01/2.45  tff(c_4807, plain, (![A_222]: (v4_relat_1(A_222, k1_relat_1(A_222)) | ~v1_funct_1(A_222) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_4782, c_20])).
% 7.01/2.45  tff(c_36, plain, (![B_19]: (v1_partfun1(B_19, k1_relat_1(B_19)) | ~v4_relat_1(B_19, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.01/2.45  tff(c_4825, plain, (![A_226]: (v1_partfun1(A_226, k1_relat_1(A_226)) | ~v1_funct_1(A_226) | ~v1_relat_1(A_226))), inference(resolution, [status(thm)], [c_4807, c_36])).
% 7.01/2.45  tff(c_4828, plain, (![A_7]: (v1_partfun1(k2_funct_1(A_7), k2_relat_1(A_7)) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4825])).
% 7.01/2.45  tff(c_5058, plain, (![A_265, B_266, C_267]: (v4_relat_1(k2_tops_2(A_265, B_266, C_267), B_266) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_2(C_267, A_265, B_266) | ~v1_funct_1(C_267))), inference(resolution, [status(thm)], [c_4975, c_20])).
% 7.01/2.45  tff(c_5064, plain, (v4_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4743, c_5058])).
% 7.01/2.45  tff(c_5069, plain, (v4_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4744, c_5064])).
% 7.01/2.45  tff(c_38, plain, (![B_19, A_18]: (k1_relat_1(B_19)=A_18 | ~v1_partfun1(B_19, A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.01/2.45  tff(c_5072, plain, (k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_5069, c_38])).
% 7.01/2.45  tff(c_5075, plain, (k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5050, c_5072])).
% 7.01/2.45  tff(c_5103, plain, (~v1_partfun1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5075])).
% 7.01/2.45  tff(c_5197, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5196, c_5103])).
% 7.01/2.45  tff(c_5337, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4828, c_5197])).
% 7.01/2.45  tff(c_5341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_80, c_72, c_5200, c_5090, c_5337])).
% 7.01/2.45  tff(c_5342, plain, (k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_5075])).
% 7.01/2.45  tff(c_4801, plain, (![A_221]: (k2_relset_1(k1_relat_1(A_221), k2_relat_1(A_221), A_221)=k2_relat_1(A_221) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(resolution, [status(thm)], [c_4782, c_22])).
% 7.01/2.45  tff(c_5359, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5342, c_4801])).
% 7.01/2.45  tff(c_5386, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5050, c_4885, c_5359])).
% 7.01/2.45  tff(c_5562, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5559, c_5559, c_5559, c_5386])).
% 7.01/2.45  tff(c_6144, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6136, c_6136, c_5562])).
% 7.01/2.45  tff(c_6126, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6116])).
% 7.01/2.45  tff(c_62, plain, (![A_32, B_33, C_34]: (k2_tops_2(A_32, B_33, C_34)=k2_funct_1(C_34) | ~v2_funct_1(C_34) | k2_relset_1(A_32, B_33, C_34)!=B_33 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.01/2.45  tff(c_5791, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5602, c_62])).
% 7.01/2.45  tff(c_5835, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5090, c_5494, c_5791])).
% 7.01/2.45  tff(c_6432, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6144, c_6126, c_5835])).
% 7.01/2.45  tff(c_4669, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_4667, c_4667, c_130])).
% 7.01/2.45  tff(c_4756, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4737, c_4737, c_4737, c_4669])).
% 7.01/2.45  tff(c_5574, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5559, c_4756])).
% 7.01/2.45  tff(c_6438, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6432, c_5574])).
% 7.01/2.45  tff(c_6459, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_6438])).
% 7.01/2.45  tff(c_6462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_80, c_72, c_4894, c_6459])).
% 7.01/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.45  
% 7.01/2.45  Inference rules
% 7.01/2.45  ----------------------
% 7.01/2.45  #Ref     : 0
% 7.01/2.45  #Sup     : 1311
% 7.01/2.45  #Fact    : 0
% 7.01/2.45  #Define  : 0
% 7.01/2.45  #Split   : 17
% 7.01/2.45  #Chain   : 0
% 7.01/2.45  #Close   : 0
% 7.01/2.45  
% 7.01/2.45  Ordering : KBO
% 7.01/2.45  
% 7.01/2.45  Simplification rules
% 7.01/2.45  ----------------------
% 7.01/2.45  #Subsume      : 85
% 7.01/2.45  #Demod        : 3756
% 7.01/2.45  #Tautology    : 769
% 7.01/2.45  #SimpNegUnit  : 12
% 7.01/2.45  #BackRed      : 173
% 7.01/2.45  
% 7.01/2.45  #Partial instantiations: 0
% 7.01/2.45  #Strategies tried      : 1
% 7.01/2.45  
% 7.01/2.45  Timing (in seconds)
% 7.01/2.45  ----------------------
% 7.01/2.45  Preprocessing        : 0.38
% 7.01/2.45  Parsing              : 0.20
% 7.01/2.45  CNF conversion       : 0.03
% 7.01/2.45  Main loop            : 1.25
% 7.01/2.45  Inferencing          : 0.40
% 7.01/2.45  Reduction            : 0.51
% 7.01/2.45  Demodulation         : 0.39
% 7.01/2.45  BG Simplification    : 0.05
% 7.01/2.45  Subsumption          : 0.21
% 7.01/2.45  Abstraction          : 0.05
% 7.01/2.45  MUC search           : 0.00
% 7.01/2.45  Cooper               : 0.00
% 7.01/2.45  Total                : 1.70
% 7.01/2.45  Index Insertion      : 0.00
% 7.01/2.45  Index Deletion       : 0.00
% 7.01/2.45  Index Matching       : 0.00
% 7.01/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
