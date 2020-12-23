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
% DateTime   : Thu Dec  3 10:20:15 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 289 expanded)
%              Number of leaves         :   32 ( 113 expanded)
%              Depth                    :   18
%              Number of atoms          :  258 (1076 expanded)
%              Number of equality atoms :   33 ( 142 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k5_lattices(A),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).

tff(f_92,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => r1_lattices(A,k4_lattices(A,B,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != k5_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_49,plain,(
    ! [A_32] :
      ( l1_lattices(A_32)
      | ~ l3_lattices(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53,plain,(
    l1_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_46,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k4_lattices(A_12,B_13,C_14),u1_struct_0(A_12))
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_lattices(A_12)
      | ~ v6_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_169,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_lattices(A_55,B_56,C_57)
      | k2_lattices(A_55,B_56,C_57) != B_56
      | ~ m1_subset_1(C_57,u1_struct_0(A_55))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l3_lattices(A_55)
      | ~ v9_lattices(A_55)
      | ~ v8_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_179,plain,(
    ! [B_56] :
      ( r1_lattices('#skF_2',B_56,'#skF_3')
      | k2_lattices('#skF_2',B_56,'#skF_3') != B_56
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_169])).

tff(c_189,plain,(
    ! [B_56] :
      ( r1_lattices('#skF_2',B_56,'#skF_3')
      | k2_lattices('#skF_2',B_56,'#skF_3') != B_56
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_179])).

tff(c_190,plain,(
    ! [B_56] :
      ( r1_lattices('#skF_2',B_56,'#skF_3')
      | k2_lattices('#skF_2',B_56,'#skF_3') != B_56
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_189])).

tff(c_191,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_194,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_191])).

tff(c_197,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_194])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_197])).

tff(c_200,plain,(
    ! [B_56] :
      ( ~ v9_lattices('#skF_2')
      | r1_lattices('#skF_2',B_56,'#skF_3')
      | k2_lattices('#skF_2',B_56,'#skF_3') != B_56
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_206,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_209,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_206])).

tff(c_212,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_209])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_212])).

tff(c_226,plain,(
    ! [B_62] :
      ( r1_lattices('#skF_2',B_62,'#skF_3')
      | k2_lattices('#skF_2',B_62,'#skF_3') != B_62
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_233,plain,(
    ! [B_13,C_14] :
      ( r1_lattices('#skF_2',k4_lattices('#skF_2',B_13,C_14),'#skF_3')
      | k2_lattices('#skF_2',k4_lattices('#skF_2',B_13,C_14),'#skF_3') != k4_lattices('#skF_2',B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_226])).

tff(c_250,plain,(
    ! [B_13,C_14] :
      ( r1_lattices('#skF_2',k4_lattices('#skF_2',B_13,C_14),'#skF_3')
      | k2_lattices('#skF_2',k4_lattices('#skF_2',B_13,C_14),'#skF_3') != k4_lattices('#skF_2',B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_233])).

tff(c_251,plain,(
    ! [B_13,C_14] :
      ( r1_lattices('#skF_2',k4_lattices('#skF_2',B_13,C_14),'#skF_3')
      | k2_lattices('#skF_2',k4_lattices('#skF_2',B_13,C_14),'#skF_3') != k4_lattices('#skF_2',B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_250])).

tff(c_384,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_397,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_384])).

tff(c_400,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_397])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_400])).

tff(c_404,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_26,plain,(
    ! [A_15] :
      ( m1_subset_1(k5_lattices(A_15),u1_struct_0(A_15))
      | ~ l1_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    v13_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,(
    ! [A_46,C_47] :
      ( k2_lattices(A_46,k5_lattices(A_46),C_47) = k5_lattices(A_46)
      | ~ m1_subset_1(C_47,u1_struct_0(A_46))
      | ~ m1_subset_1(k5_lattices(A_46),u1_struct_0(A_46))
      | ~ v13_lattices(A_46)
      | ~ l1_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_76,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_82,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_44,c_76])).

tff(c_83,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_82])).

tff(c_84,plain,(
    ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_87,plain,
    ( ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_90,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_90])).

tff(c_94,plain,(
    m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_201,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_216,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_36,plain,(
    ! [A_24,B_28,C_30] :
      ( r1_lattices(A_24,k4_lattices(A_24,B_28,C_30),B_28)
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | ~ v8_lattices(A_24)
      | ~ v6_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_202,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_lattices(A_58,B_59,C_60) = B_59
      | ~ r1_lattices(A_58,B_59,C_60)
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l3_lattices(A_58)
      | ~ v9_lattices(A_58)
      | ~ v8_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_502,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_lattices(A_102,k4_lattices(A_102,B_103,C_104),B_103) = k4_lattices(A_102,B_103,C_104)
      | ~ m1_subset_1(k4_lattices(A_102,B_103,C_104),u1_struct_0(A_102))
      | ~ v9_lattices(A_102)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l3_lattices(A_102)
      | ~ v8_lattices(A_102)
      | ~ v6_lattices(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_36,c_202])).

tff(c_506,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_lattices(A_105,k4_lattices(A_105,B_106,C_107),B_106) = k4_lattices(A_105,B_106,C_107)
      | ~ v9_lattices(A_105)
      | ~ l3_lattices(A_105)
      | ~ v8_lattices(A_105)
      | ~ m1_subset_1(C_107,u1_struct_0(A_105))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l1_lattices(A_105)
      | ~ v6_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_24,c_502])).

tff(c_516,plain,(
    ! [B_106] :
      ( k2_lattices('#skF_2',k4_lattices('#skF_2',B_106,'#skF_3'),B_106) = k4_lattices('#skF_2',B_106,'#skF_3')
      | ~ v9_lattices('#skF_2')
      | ~ l3_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | ~ m1_subset_1(B_106,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_506])).

tff(c_526,plain,(
    ! [B_106] :
      ( k2_lattices('#skF_2',k4_lattices('#skF_2',B_106,'#skF_3'),B_106) = k4_lattices('#skF_2',B_106,'#skF_3')
      | ~ m1_subset_1(B_106,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_53,c_201,c_42,c_216,c_516])).

tff(c_528,plain,(
    ! [B_108] :
      ( k2_lattices('#skF_2',k4_lattices('#skF_2',B_108,'#skF_3'),B_108) = k4_lattices('#skF_2',B_108,'#skF_3')
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_526])).

tff(c_539,plain,
    ( k2_lattices('#skF_2',k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3'),k5_lattices('#skF_2')) = k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_528])).

tff(c_553,plain,
    ( k2_lattices('#skF_2',k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3'),k5_lattices('#skF_2')) = k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_539])).

tff(c_554,plain,(
    k2_lattices('#skF_2',k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3'),k5_lattices('#skF_2')) = k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_553])).

tff(c_109,plain,(
    ! [A_48,C_49] :
      ( k2_lattices(A_48,C_49,k5_lattices(A_48)) = k5_lattices(A_48)
      | ~ m1_subset_1(C_49,u1_struct_0(A_48))
      | ~ m1_subset_1(k5_lattices(A_48),u1_struct_0(A_48))
      | ~ v13_lattices(A_48)
      | ~ l1_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_455,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_lattices(A_91,k4_lattices(A_91,B_92,C_93),k5_lattices(A_91)) = k5_lattices(A_91)
      | ~ m1_subset_1(k5_lattices(A_91),u1_struct_0(A_91))
      | ~ v13_lattices(A_91)
      | ~ m1_subset_1(C_93,u1_struct_0(A_91))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_lattices(A_91)
      | ~ v6_lattices(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_464,plain,(
    ! [A_15,B_92,C_93] :
      ( k2_lattices(A_15,k4_lattices(A_15,B_92,C_93),k5_lattices(A_15)) = k5_lattices(A_15)
      | ~ v13_lattices(A_15)
      | ~ m1_subset_1(C_93,u1_struct_0(A_15))
      | ~ m1_subset_1(B_92,u1_struct_0(A_15))
      | ~ v6_lattices(A_15)
      | ~ l1_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_455])).

tff(c_563,plain,
    ( k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ v13_lattices('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v6_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_464])).

tff(c_576,plain,
    ( k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_404,c_94,c_40,c_44,c_563])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 3.04/1.47  
% 3.04/1.47  %Foreground sorts:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Background operators:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Foreground operators:
% 3.04/1.47  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.04/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.04/1.47  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.04/1.47  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.47  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.04/1.47  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.04/1.47  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.04/1.47  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.04/1.47  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.04/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.47  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.04/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.47  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.04/1.47  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.47  tff(v13_lattices, type, v13_lattices: $i > $o).
% 3.04/1.47  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.47  tff(k5_lattices, type, k5_lattices: $i > $i).
% 3.04/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.47  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.04/1.47  
% 3.17/1.49  tff(f_143, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k5_lattices(A), B) = k5_lattices(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattices)).
% 3.17/1.49  tff(f_92, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.17/1.49  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.17/1.49  tff(f_79, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k4_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_lattices)).
% 3.17/1.49  tff(f_111, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 3.17/1.49  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 3.17/1.49  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 3.17/1.49  tff(f_128, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 3.17/1.49  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_38, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!=k5_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_42, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_49, plain, (![A_32]: (l1_lattices(A_32) | ~l3_lattices(A_32))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.49  tff(c_53, plain, (l1_lattices('#skF_2')), inference(resolution, [status(thm)], [c_42, c_49])).
% 3.17/1.49  tff(c_46, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.49  tff(c_24, plain, (![A_12, B_13, C_14]: (m1_subset_1(k4_lattices(A_12, B_13, C_14), u1_struct_0(A_12)) | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l1_lattices(A_12) | ~v6_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.17/1.49  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.49  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.49  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_169, plain, (![A_55, B_56, C_57]: (r1_lattices(A_55, B_56, C_57) | k2_lattices(A_55, B_56, C_57)!=B_56 | ~m1_subset_1(C_57, u1_struct_0(A_55)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l3_lattices(A_55) | ~v9_lattices(A_55) | ~v8_lattices(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.49  tff(c_179, plain, (![B_56]: (r1_lattices('#skF_2', B_56, '#skF_3') | k2_lattices('#skF_2', B_56, '#skF_3')!=B_56 | ~m1_subset_1(B_56, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_169])).
% 3.17/1.49  tff(c_189, plain, (![B_56]: (r1_lattices('#skF_2', B_56, '#skF_3') | k2_lattices('#skF_2', B_56, '#skF_3')!=B_56 | ~m1_subset_1(B_56, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_179])).
% 3.17/1.49  tff(c_190, plain, (![B_56]: (r1_lattices('#skF_2', B_56, '#skF_3') | k2_lattices('#skF_2', B_56, '#skF_3')!=B_56 | ~m1_subset_1(B_56, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_189])).
% 3.17/1.49  tff(c_191, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_190])).
% 3.17/1.49  tff(c_194, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_191])).
% 3.17/1.49  tff(c_197, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_194])).
% 3.17/1.49  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_197])).
% 3.17/1.49  tff(c_200, plain, (![B_56]: (~v9_lattices('#skF_2') | r1_lattices('#skF_2', B_56, '#skF_3') | k2_lattices('#skF_2', B_56, '#skF_3')!=B_56 | ~m1_subset_1(B_56, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_190])).
% 3.17/1.49  tff(c_206, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_200])).
% 3.17/1.49  tff(c_209, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_206])).
% 3.17/1.49  tff(c_212, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_209])).
% 3.17/1.49  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_212])).
% 3.17/1.49  tff(c_226, plain, (![B_62]: (r1_lattices('#skF_2', B_62, '#skF_3') | k2_lattices('#skF_2', B_62, '#skF_3')!=B_62 | ~m1_subset_1(B_62, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_200])).
% 3.17/1.49  tff(c_233, plain, (![B_13, C_14]: (r1_lattices('#skF_2', k4_lattices('#skF_2', B_13, C_14), '#skF_3') | k2_lattices('#skF_2', k4_lattices('#skF_2', B_13, C_14), '#skF_3')!=k4_lattices('#skF_2', B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0('#skF_2')) | ~m1_subset_1(B_13, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_226])).
% 3.17/1.49  tff(c_250, plain, (![B_13, C_14]: (r1_lattices('#skF_2', k4_lattices('#skF_2', B_13, C_14), '#skF_3') | k2_lattices('#skF_2', k4_lattices('#skF_2', B_13, C_14), '#skF_3')!=k4_lattices('#skF_2', B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0('#skF_2')) | ~m1_subset_1(B_13, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_233])).
% 3.17/1.49  tff(c_251, plain, (![B_13, C_14]: (r1_lattices('#skF_2', k4_lattices('#skF_2', B_13, C_14), '#skF_3') | k2_lattices('#skF_2', k4_lattices('#skF_2', B_13, C_14), '#skF_3')!=k4_lattices('#skF_2', B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0('#skF_2')) | ~m1_subset_1(B_13, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_250])).
% 3.17/1.49  tff(c_384, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_251])).
% 3.17/1.49  tff(c_397, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_384])).
% 3.17/1.49  tff(c_400, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_397])).
% 3.17/1.49  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_400])).
% 3.17/1.49  tff(c_404, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_251])).
% 3.17/1.49  tff(c_26, plain, (![A_15]: (m1_subset_1(k5_lattices(A_15), u1_struct_0(A_15)) | ~l1_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.49  tff(c_44, plain, (v13_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_68, plain, (![A_46, C_47]: (k2_lattices(A_46, k5_lattices(A_46), C_47)=k5_lattices(A_46) | ~m1_subset_1(C_47, u1_struct_0(A_46)) | ~m1_subset_1(k5_lattices(A_46), u1_struct_0(A_46)) | ~v13_lattices(A_46) | ~l1_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.49  tff(c_76, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_68])).
% 3.17/1.49  tff(c_82, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_44, c_76])).
% 3.17/1.49  tff(c_83, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_82])).
% 3.17/1.49  tff(c_84, plain, (~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_83])).
% 3.17/1.49  tff(c_87, plain, (~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_84])).
% 3.17/1.49  tff(c_90, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_87])).
% 3.17/1.49  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_90])).
% 3.17/1.49  tff(c_94, plain, (m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_83])).
% 3.17/1.49  tff(c_201, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_190])).
% 3.17/1.49  tff(c_216, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_200])).
% 3.17/1.49  tff(c_36, plain, (![A_24, B_28, C_30]: (r1_lattices(A_24, k4_lattices(A_24, B_28, C_30), B_28) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l3_lattices(A_24) | ~v8_lattices(A_24) | ~v6_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.17/1.49  tff(c_202, plain, (![A_58, B_59, C_60]: (k2_lattices(A_58, B_59, C_60)=B_59 | ~r1_lattices(A_58, B_59, C_60) | ~m1_subset_1(C_60, u1_struct_0(A_58)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l3_lattices(A_58) | ~v9_lattices(A_58) | ~v8_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.49  tff(c_502, plain, (![A_102, B_103, C_104]: (k2_lattices(A_102, k4_lattices(A_102, B_103, C_104), B_103)=k4_lattices(A_102, B_103, C_104) | ~m1_subset_1(k4_lattices(A_102, B_103, C_104), u1_struct_0(A_102)) | ~v9_lattices(A_102) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l3_lattices(A_102) | ~v8_lattices(A_102) | ~v6_lattices(A_102) | v2_struct_0(A_102))), inference(resolution, [status(thm)], [c_36, c_202])).
% 3.17/1.49  tff(c_506, plain, (![A_105, B_106, C_107]: (k2_lattices(A_105, k4_lattices(A_105, B_106, C_107), B_106)=k4_lattices(A_105, B_106, C_107) | ~v9_lattices(A_105) | ~l3_lattices(A_105) | ~v8_lattices(A_105) | ~m1_subset_1(C_107, u1_struct_0(A_105)) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~l1_lattices(A_105) | ~v6_lattices(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_24, c_502])).
% 3.17/1.49  tff(c_516, plain, (![B_106]: (k2_lattices('#skF_2', k4_lattices('#skF_2', B_106, '#skF_3'), B_106)=k4_lattices('#skF_2', B_106, '#skF_3') | ~v9_lattices('#skF_2') | ~l3_lattices('#skF_2') | ~v8_lattices('#skF_2') | ~m1_subset_1(B_106, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_506])).
% 3.17/1.49  tff(c_526, plain, (![B_106]: (k2_lattices('#skF_2', k4_lattices('#skF_2', B_106, '#skF_3'), B_106)=k4_lattices('#skF_2', B_106, '#skF_3') | ~m1_subset_1(B_106, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_53, c_201, c_42, c_216, c_516])).
% 3.17/1.49  tff(c_528, plain, (![B_108]: (k2_lattices('#skF_2', k4_lattices('#skF_2', B_108, '#skF_3'), B_108)=k4_lattices('#skF_2', B_108, '#skF_3') | ~m1_subset_1(B_108, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_526])).
% 3.17/1.49  tff(c_539, plain, (k2_lattices('#skF_2', k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3'), k5_lattices('#skF_2'))=k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_528])).
% 3.17/1.49  tff(c_553, plain, (k2_lattices('#skF_2', k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3'), k5_lattices('#skF_2'))=k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_539])).
% 3.17/1.49  tff(c_554, plain, (k2_lattices('#skF_2', k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3'), k5_lattices('#skF_2'))=k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_553])).
% 3.17/1.49  tff(c_109, plain, (![A_48, C_49]: (k2_lattices(A_48, C_49, k5_lattices(A_48))=k5_lattices(A_48) | ~m1_subset_1(C_49, u1_struct_0(A_48)) | ~m1_subset_1(k5_lattices(A_48), u1_struct_0(A_48)) | ~v13_lattices(A_48) | ~l1_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.49  tff(c_455, plain, (![A_91, B_92, C_93]: (k2_lattices(A_91, k4_lattices(A_91, B_92, C_93), k5_lattices(A_91))=k5_lattices(A_91) | ~m1_subset_1(k5_lattices(A_91), u1_struct_0(A_91)) | ~v13_lattices(A_91) | ~m1_subset_1(C_93, u1_struct_0(A_91)) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_lattices(A_91) | ~v6_lattices(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_24, c_109])).
% 3.17/1.49  tff(c_464, plain, (![A_15, B_92, C_93]: (k2_lattices(A_15, k4_lattices(A_15, B_92, C_93), k5_lattices(A_15))=k5_lattices(A_15) | ~v13_lattices(A_15) | ~m1_subset_1(C_93, u1_struct_0(A_15)) | ~m1_subset_1(B_92, u1_struct_0(A_15)) | ~v6_lattices(A_15) | ~l1_lattices(A_15) | v2_struct_0(A_15))), inference(resolution, [status(thm)], [c_26, c_455])).
% 3.17/1.49  tff(c_563, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~v13_lattices('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_554, c_464])).
% 3.17/1.49  tff(c_576, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_404, c_94, c_40, c_44, c_563])).
% 3.17/1.49  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_576])).
% 3.17/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.49  
% 3.17/1.49  Inference rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Ref     : 0
% 3.17/1.49  #Sup     : 100
% 3.17/1.49  #Fact    : 0
% 3.17/1.49  #Define  : 0
% 3.17/1.49  #Split   : 5
% 3.17/1.49  #Chain   : 0
% 3.17/1.49  #Close   : 0
% 3.17/1.49  
% 3.17/1.49  Ordering : KBO
% 3.17/1.49  
% 3.17/1.49  Simplification rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Subsume      : 6
% 3.17/1.49  #Demod        : 110
% 3.17/1.49  #Tautology    : 49
% 3.17/1.49  #SimpNegUnit  : 40
% 3.17/1.49  #BackRed      : 0
% 3.17/1.49  
% 3.17/1.49  #Partial instantiations: 0
% 3.17/1.49  #Strategies tried      : 1
% 3.17/1.49  
% 3.17/1.49  Timing (in seconds)
% 3.17/1.49  ----------------------
% 3.17/1.49  Preprocessing        : 0.32
% 3.17/1.49  Parsing              : 0.18
% 3.17/1.49  CNF conversion       : 0.02
% 3.17/1.49  Main loop            : 0.34
% 3.17/1.49  Inferencing          : 0.14
% 3.17/1.49  Reduction            : 0.09
% 3.17/1.49  Demodulation         : 0.06
% 3.17/1.49  BG Simplification    : 0.02
% 3.17/1.49  Subsumption          : 0.07
% 3.17/1.49  Abstraction          : 0.02
% 3.17/1.49  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.70
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
