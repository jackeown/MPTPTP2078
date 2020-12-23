%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:23 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  168 (2011 expanded)
%              Number of leaves         :   25 ( 705 expanded)
%              Depth                    :   17
%              Number of atoms          :  416 (8282 expanded)
%              Number of equality atoms :  101 (1772 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                 => ( ( v1_borsuk_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_borsuk_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_59,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_30,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_85,plain,(
    ! [A_33] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_93,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_pre_topc(A_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_756,plain,(
    ! [D_99,B_100,C_101,A_102] :
      ( D_99 = B_100
      | g1_pre_topc(C_101,D_99) != g1_pre_topc(A_102,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k1_zfmisc_1(A_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_765,plain,(
    ! [B_103,A_104] :
      ( u1_pre_topc('#skF_2') = B_103
      | g1_pre_topc(A_104,B_103) != '#skF_3'
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_756])).

tff(c_770,plain,(
    ! [A_105] :
      ( u1_pre_topc(A_105) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)) != '#skF_3'
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_4,c_765])).

tff(c_782,plain,(
    ! [A_106] :
      ( u1_pre_topc(A_106) = u1_pre_topc('#skF_2')
      | A_106 != '#skF_3'
      | ~ l1_pre_topc(A_106)
      | ~ v1_pre_topc(A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_770])).

tff(c_785,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_782])).

tff(c_791,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_785])).

tff(c_796,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_26])).

tff(c_12,plain,(
    ! [C_8,A_4,D_9,B_5] :
      ( C_8 = A_4
      | g1_pre_topc(C_8,D_9) != g1_pre_topc(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_877,plain,(
    ! [A_116,B_117] :
      ( u1_struct_0('#skF_2') = A_116
      | g1_pre_topc(A_116,B_117) != '#skF_3'
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k1_zfmisc_1(A_116))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_12])).

tff(c_889,plain,(
    ! [A_118] :
      ( u1_struct_0(A_118) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_118),u1_pre_topc(A_118)) != '#skF_3'
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_4,c_877])).

tff(c_900,plain,(
    ! [A_119] :
      ( u1_struct_0(A_119) = u1_struct_0('#skF_2')
      | A_119 != '#skF_3'
      | ~ l1_pre_topc(A_119)
      | ~ v1_pre_topc(A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_889])).

tff(c_903,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_900])).

tff(c_909,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_903])).

tff(c_915,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_796])).

tff(c_1031,plain,(
    ! [C_123,A_124] :
      ( m1_pre_topc(C_123,A_124)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_123),u1_pre_topc(C_123)),A_124)
      | ~ l1_pre_topc(C_123)
      | ~ v2_pre_topc(C_123)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_123),u1_pre_topc(C_123)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_123),u1_pre_topc(C_123)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1040,plain,(
    ! [A_124] :
      ( m1_pre_topc('#skF_2',A_124)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')),A_124)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_1031])).

tff(c_1050,plain,(
    ! [A_125] :
      ( m1_pre_topc('#skF_2',A_125)
      | ~ m1_pre_topc('#skF_3',A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_915,c_909,c_791,c_28,c_915,c_909,c_791,c_34,c_32,c_915,c_909,c_1040])).

tff(c_112,plain,(
    ! [C_37,A_38,D_39,B_40] :
      ( C_37 = A_38
      | g1_pre_topc(C_37,D_39) != g1_pre_topc(A_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_120,plain,(
    ! [C_37,D_39] :
      ( u1_struct_0('#skF_2') = C_37
      | g1_pre_topc(C_37,D_39) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_112])).

tff(c_155,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_158])).

tff(c_165,plain,(
    ! [C_50,D_51] :
      ( u1_struct_0('#skF_2') = C_50
      | g1_pre_topc(C_50,D_51) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_182,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = u1_struct_0('#skF_2')
      | A_52 != '#skF_3'
      | ~ v1_pre_topc(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_185,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_182])).

tff(c_191,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_185])).

tff(c_164,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_194,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_164])).

tff(c_125,plain,(
    ! [D_41,B_42,C_43,A_44] :
      ( D_41 = B_42
      | g1_pre_topc(C_43,D_41) != g1_pre_topc(A_44,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    ! [D_41,C_43] :
      ( u1_pre_topc('#skF_2') = D_41
      | g1_pre_topc(C_43,D_41) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_125])).

tff(c_257,plain,(
    ! [D_41,C_43] :
      ( u1_pre_topc('#skF_2') = D_41
      | g1_pre_topc(C_43,D_41) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_133])).

tff(c_258,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_258])).

tff(c_309,plain,(
    ! [D_61,C_62] :
      ( u1_pre_topc('#skF_2') = D_61
      | g1_pre_topc(C_62,D_61) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_351,plain,(
    ! [A_65] :
      ( u1_pre_topc(A_65) = u1_pre_topc('#skF_2')
      | A_65 != '#skF_3'
      | ~ v1_pre_topc(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_309])).

tff(c_354,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_351])).

tff(c_360,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_354])).

tff(c_196,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_26])).

tff(c_374,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_196])).

tff(c_461,plain,(
    ! [C_71,A_72] :
      ( m1_pre_topc(C_71,A_72)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_71),u1_pre_topc(C_71)),A_72)
      | ~ l1_pre_topc(C_71)
      | ~ v2_pre_topc(C_71)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_71),u1_pre_topc(C_71)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_71),u1_pre_topc(C_71)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_473,plain,(
    ! [A_72] :
      ( m1_pre_topc('#skF_2',A_72)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_72)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_461])).

tff(c_483,plain,(
    ! [A_72] :
      ( m1_pre_topc('#skF_2',A_72)
      | ~ m1_pre_topc('#skF_3',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_374,c_360,c_191,c_28,c_374,c_360,c_191,c_34,c_32,c_374,c_360,c_473])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56,plain,
    ( v1_borsuk_1('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_57,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_24,plain,(
    ! [B_26,A_24] :
      ( m1_subset_1(u1_struct_0(B_26),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_229,plain,(
    ! [B_53,A_54] :
      ( v4_pre_topc(u1_struct_0(B_53),A_54)
      | ~ v1_borsuk_1(B_53,A_54)
      | ~ m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_242,plain,(
    ! [B_26,A_24] :
      ( v4_pre_topc(u1_struct_0(B_26),A_24)
      | ~ v1_borsuk_1(B_26,A_24)
      | ~ v2_pre_topc(A_24)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_229])).

tff(c_295,plain,(
    ! [B_59,A_60] :
      ( v1_borsuk_1(B_59,A_60)
      | ~ v4_pre_topc(u1_struct_0(B_59),A_60)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_525,plain,(
    ! [B_76,A_77] :
      ( v1_borsuk_1(B_76,A_77)
      | ~ v4_pre_topc(u1_struct_0(B_76),A_77)
      | ~ v2_pre_topc(A_77)
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_24,c_295])).

tff(c_564,plain,(
    ! [A_82] :
      ( v1_borsuk_1('#skF_2',A_82)
      | ~ v4_pre_topc(u1_struct_0('#skF_3'),A_82)
      | ~ v2_pre_topc(A_82)
      | ~ m1_pre_topc('#skF_2',A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_525])).

tff(c_726,plain,(
    ! [A_95] :
      ( v1_borsuk_1('#skF_2',A_95)
      | ~ m1_pre_topc('#skF_2',A_95)
      | ~ v1_borsuk_1('#skF_3',A_95)
      | ~ v2_pre_topc(A_95)
      | ~ m1_pre_topc('#skF_3',A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_242,c_564])).

tff(c_40,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_96,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_59,c_40])).

tff(c_97,plain,(
    ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_729,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_726,c_97])).

tff(c_732,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_38,c_57,c_729])).

tff(c_735,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_483,c_732])).

tff(c_739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_735])).

tff(c_740,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1056,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1050,c_740])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_1056])).

tff(c_1065,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1064,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1072,plain,(
    ! [A_127] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_127),u1_pre_topc(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1075,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1072])).

tff(c_1077,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1075])).

tff(c_1158,plain,(
    ! [D_140,B_141,C_142,A_143] :
      ( D_140 = B_141
      | g1_pre_topc(C_142,D_140) != g1_pre_topc(A_143,B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k1_zfmisc_1(A_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1216,plain,(
    ! [B_144,A_145] :
      ( u1_pre_topc('#skF_2') = B_144
      | g1_pre_topc(A_145,B_144) != '#skF_3'
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k1_zfmisc_1(A_145))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1158])).

tff(c_1264,plain,(
    ! [A_150] :
      ( u1_pre_topc(A_150) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_150),u1_pre_topc(A_150)) != '#skF_3'
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_4,c_1216])).

tff(c_1275,plain,(
    ! [A_151] :
      ( u1_pre_topc(A_151) = u1_pre_topc('#skF_2')
      | A_151 != '#skF_3'
      | ~ l1_pre_topc(A_151)
      | ~ v1_pre_topc(A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1264])).

tff(c_1278,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1077,c_1275])).

tff(c_1284,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1278])).

tff(c_1117,plain,(
    ! [C_132,A_133,D_134,B_135] :
      ( C_132 = A_133
      | g1_pre_topc(C_132,D_134) != g1_pre_topc(A_133,B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k1_zfmisc_1(A_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1126,plain,(
    ! [A_136,B_137] :
      ( u1_struct_0('#skF_2') = A_136
      | g1_pre_topc(A_136,B_137) != '#skF_3'
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k1_zfmisc_1(A_136))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1117])).

tff(c_1131,plain,(
    ! [A_138] :
      ( u1_struct_0(A_138) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_138),u1_pre_topc(A_138)) != '#skF_3'
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_4,c_1126])).

tff(c_1143,plain,(
    ! [A_139] :
      ( u1_struct_0(A_139) = u1_struct_0('#skF_2')
      | A_139 != '#skF_3'
      | ~ l1_pre_topc(A_139)
      | ~ v1_pre_topc(A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1131])).

tff(c_1146,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1077,c_1143])).

tff(c_1152,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1146])).

tff(c_1170,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_26])).

tff(c_1300,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1170])).

tff(c_1464,plain,(
    ! [C_166,A_167] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_166),u1_pre_topc(C_166)),A_167)
      | ~ m1_pre_topc(C_166,A_167)
      | ~ l1_pre_topc(C_166)
      | ~ v2_pre_topc(C_166)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_166),u1_pre_topc(C_166)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_166),u1_pre_topc(C_166)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1473,plain,(
    ! [A_167] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')),A_167)
      | ~ m1_pre_topc('#skF_2',A_167)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_1464])).

tff(c_1487,plain,(
    ! [A_168] :
      ( m1_pre_topc('#skF_3',A_168)
      | ~ m1_pre_topc('#skF_2',A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1300,c_1284,c_1152,c_28,c_1300,c_1284,c_1152,c_34,c_32,c_1300,c_1152,c_1473])).

tff(c_1493,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1064,c_1487])).

tff(c_1497,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1493])).

tff(c_1499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_1497])).

tff(c_1501,plain,(
    ~ v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1502,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1501,c_54])).

tff(c_1529,plain,(
    ! [A_171] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_171),u1_pre_topc(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1535,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1529])).

tff(c_1537,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1535])).

tff(c_1555,plain,(
    ! [C_175,A_176,D_177,B_178] :
      ( C_175 = A_176
      | g1_pre_topc(C_175,D_177) != g1_pre_topc(A_176,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(k1_zfmisc_1(A_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1563,plain,(
    ! [C_175,D_177] :
      ( u1_struct_0('#skF_2') = C_175
      | g1_pre_topc(C_175,D_177) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1555])).

tff(c_1609,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1563])).

tff(c_1612,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_1609])).

tff(c_1616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1612])).

tff(c_1619,plain,(
    ! [C_189,D_190] :
      ( u1_struct_0('#skF_2') = C_189
      | g1_pre_topc(C_189,D_190) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_1563])).

tff(c_1636,plain,(
    ! [A_191] :
      ( u1_struct_0(A_191) = u1_struct_0('#skF_2')
      | A_191 != '#skF_3'
      | ~ v1_pre_topc(A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1619])).

tff(c_1639,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1537,c_1636])).

tff(c_1645,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1639])).

tff(c_1618,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1563])).

tff(c_1648,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1618])).

tff(c_1573,plain,(
    ! [D_181,B_182,C_183,A_184] :
      ( D_181 = B_182
      | g1_pre_topc(C_183,D_181) != g1_pre_topc(A_184,B_182)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k1_zfmisc_1(A_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1581,plain,(
    ! [D_181,C_183] :
      ( u1_pre_topc('#skF_2') = D_181
      | g1_pre_topc(C_183,D_181) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1573])).

tff(c_1717,plain,(
    ! [D_181,C_183] :
      ( u1_pre_topc('#skF_2') = D_181
      | g1_pre_topc(C_183,D_181) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1581])).

tff(c_1718,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1717])).

tff(c_1736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1648,c_1718])).

tff(c_1769,plain,(
    ! [D_200,C_201] :
      ( u1_pre_topc('#skF_2') = D_200
      | g1_pre_topc(C_201,D_200) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_1717])).

tff(c_1811,plain,(
    ! [A_204] :
      ( u1_pre_topc(A_204) = u1_pre_topc('#skF_2')
      | A_204 != '#skF_3'
      | ~ v1_pre_topc(A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1769])).

tff(c_1814,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1537,c_1811])).

tff(c_1820,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1814])).

tff(c_1650,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_26])).

tff(c_1834,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_1650])).

tff(c_1928,plain,(
    ! [C_210,A_211] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_210),u1_pre_topc(C_210)),A_211)
      | ~ m1_pre_topc(C_210,A_211)
      | ~ l1_pre_topc(C_210)
      | ~ v2_pre_topc(C_210)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_210),u1_pre_topc(C_210)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_210),u1_pre_topc(C_210)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1940,plain,(
    ! [A_211] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_211)
      | ~ m1_pre_topc('#skF_2',A_211)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_1928])).

tff(c_1951,plain,(
    ! [A_212] :
      ( m1_pre_topc('#skF_3',A_212)
      | ~ m1_pre_topc('#skF_2',A_212)
      | ~ l1_pre_topc(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1834,c_1820,c_1645,c_28,c_1834,c_1820,c_1645,c_34,c_32,c_1834,c_1820,c_1940])).

tff(c_1957,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1502,c_1951])).

tff(c_1961,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1957])).

tff(c_1500,plain,(
    v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1755,plain,(
    ! [B_198,A_199] :
      ( v4_pre_topc(u1_struct_0(B_198),A_199)
      | ~ v1_borsuk_1(B_198,A_199)
      | ~ m1_subset_1(u1_struct_0(B_198),k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ m1_pre_topc(B_198,A_199)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1991,plain,(
    ! [B_215,A_216] :
      ( v4_pre_topc(u1_struct_0(B_215),A_216)
      | ~ v1_borsuk_1(B_215,A_216)
      | ~ v2_pre_topc(A_216)
      | ~ m1_pre_topc(B_215,A_216)
      | ~ l1_pre_topc(A_216) ) ),
    inference(resolution,[status(thm)],[c_24,c_1755])).

tff(c_2032,plain,(
    ! [A_221] :
      ( v4_pre_topc(u1_struct_0('#skF_3'),A_221)
      | ~ v1_borsuk_1('#skF_2',A_221)
      | ~ v2_pre_topc(A_221)
      | ~ m1_pre_topc('#skF_2',A_221)
      | ~ l1_pre_topc(A_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_1991])).

tff(c_1689,plain,(
    ! [B_192,A_193] :
      ( v1_borsuk_1(B_192,A_193)
      | ~ v4_pre_topc(u1_struct_0(B_192),A_193)
      | ~ m1_subset_1(u1_struct_0(B_192),k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ m1_pre_topc(B_192,A_193)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1702,plain,(
    ! [B_26,A_24] :
      ( v1_borsuk_1(B_26,A_24)
      | ~ v4_pre_topc(u1_struct_0(B_26),A_24)
      | ~ v2_pre_topc(A_24)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_1689])).

tff(c_2192,plain,(
    ! [A_234] :
      ( v1_borsuk_1('#skF_3',A_234)
      | ~ m1_pre_topc('#skF_3',A_234)
      | ~ v1_borsuk_1('#skF_2',A_234)
      | ~ v2_pre_topc(A_234)
      | ~ m1_pre_topc('#skF_2',A_234)
      | ~ l1_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_2032,c_1702])).

tff(c_2195,plain,
    ( v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1500,c_2192])).

tff(c_2198,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1502,c_38,c_1961,c_2195])).

tff(c_2200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1501,c_2198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.64  
% 3.92/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.65  %$ v4_pre_topc > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.65  
% 3.92/1.65  %Foreground sorts:
% 3.92/1.65  
% 3.92/1.65  
% 3.92/1.65  %Background operators:
% 3.92/1.65  
% 3.92/1.65  
% 3.92/1.65  %Foreground operators:
% 3.92/1.65  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.92/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.65  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.92/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.92/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.92/1.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.92/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.92/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.92/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.92/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.92/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.65  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.92/1.65  
% 3.92/1.67  tff(f_120, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> (v1_borsuk_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tmap_1)).
% 3.92/1.67  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 3.92/1.67  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.92/1.67  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.92/1.67  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.92/1.67  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 3.92/1.67  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.92/1.67  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 3.92/1.67  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_48, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_59, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.92/1.67  tff(c_30, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_85, plain, (![A_33]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.67  tff(c_91, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_85])).
% 3.92/1.67  tff(c_93, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_91])).
% 3.92/1.67  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.92/1.67  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_pre_topc(A_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2)))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.67  tff(c_756, plain, (![D_99, B_100, C_101, A_102]: (D_99=B_100 | g1_pre_topc(C_101, D_99)!=g1_pre_topc(A_102, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k1_zfmisc_1(A_102))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_765, plain, (![B_103, A_104]: (u1_pre_topc('#skF_2')=B_103 | g1_pre_topc(A_104, B_103)!='#skF_3' | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_756])).
% 3.92/1.67  tff(c_770, plain, (![A_105]: (u1_pre_topc(A_105)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))!='#skF_3' | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_4, c_765])).
% 3.92/1.67  tff(c_782, plain, (![A_106]: (u1_pre_topc(A_106)=u1_pre_topc('#skF_2') | A_106!='#skF_3' | ~l1_pre_topc(A_106) | ~v1_pre_topc(A_106) | ~l1_pre_topc(A_106))), inference(superposition, [status(thm), theory('equality')], [c_2, c_770])).
% 3.92/1.67  tff(c_785, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_782])).
% 3.92/1.67  tff(c_791, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_785])).
% 3.92/1.67  tff(c_796, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_791, c_26])).
% 3.92/1.67  tff(c_12, plain, (![C_8, A_4, D_9, B_5]: (C_8=A_4 | g1_pre_topc(C_8, D_9)!=g1_pre_topc(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_877, plain, (![A_116, B_117]: (u1_struct_0('#skF_2')=A_116 | g1_pre_topc(A_116, B_117)!='#skF_3' | ~m1_subset_1(B_117, k1_zfmisc_1(k1_zfmisc_1(A_116))))), inference(superposition, [status(thm), theory('equality')], [c_796, c_12])).
% 3.92/1.67  tff(c_889, plain, (![A_118]: (u1_struct_0(A_118)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_118), u1_pre_topc(A_118))!='#skF_3' | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_4, c_877])).
% 3.92/1.67  tff(c_900, plain, (![A_119]: (u1_struct_0(A_119)=u1_struct_0('#skF_2') | A_119!='#skF_3' | ~l1_pre_topc(A_119) | ~v1_pre_topc(A_119) | ~l1_pre_topc(A_119))), inference(superposition, [status(thm), theory('equality')], [c_2, c_889])).
% 3.92/1.67  tff(c_903, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_900])).
% 3.92/1.67  tff(c_909, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_903])).
% 3.92/1.67  tff(c_915, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_909, c_796])).
% 3.92/1.67  tff(c_1031, plain, (![C_123, A_124]: (m1_pre_topc(C_123, A_124) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_123), u1_pre_topc(C_123)), A_124) | ~l1_pre_topc(C_123) | ~v2_pre_topc(C_123) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_123), u1_pre_topc(C_123))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_123), u1_pre_topc(C_123))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.92/1.67  tff(c_1040, plain, (![A_124]: (m1_pre_topc('#skF_2', A_124) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3')), A_124) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_124))), inference(superposition, [status(thm), theory('equality')], [c_791, c_1031])).
% 3.92/1.67  tff(c_1050, plain, (![A_125]: (m1_pre_topc('#skF_2', A_125) | ~m1_pre_topc('#skF_3', A_125) | ~l1_pre_topc(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_915, c_909, c_791, c_28, c_915, c_909, c_791, c_34, c_32, c_915, c_909, c_1040])).
% 3.92/1.67  tff(c_112, plain, (![C_37, A_38, D_39, B_40]: (C_37=A_38 | g1_pre_topc(C_37, D_39)!=g1_pre_topc(A_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_120, plain, (![C_37, D_39]: (u1_struct_0('#skF_2')=C_37 | g1_pre_topc(C_37, D_39)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_112])).
% 3.92/1.67  tff(c_155, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_120])).
% 3.92/1.67  tff(c_158, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_155])).
% 3.92/1.67  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_158])).
% 3.92/1.67  tff(c_165, plain, (![C_50, D_51]: (u1_struct_0('#skF_2')=C_50 | g1_pre_topc(C_50, D_51)!='#skF_3')), inference(splitRight, [status(thm)], [c_120])).
% 3.92/1.67  tff(c_182, plain, (![A_52]: (u1_struct_0(A_52)=u1_struct_0('#skF_2') | A_52!='#skF_3' | ~v1_pre_topc(A_52) | ~l1_pre_topc(A_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_165])).
% 3.92/1.67  tff(c_185, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_182])).
% 3.92/1.67  tff(c_191, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_185])).
% 3.92/1.67  tff(c_164, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_120])).
% 3.92/1.67  tff(c_194, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_164])).
% 3.92/1.67  tff(c_125, plain, (![D_41, B_42, C_43, A_44]: (D_41=B_42 | g1_pre_topc(C_43, D_41)!=g1_pre_topc(A_44, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_133, plain, (![D_41, C_43]: (u1_pre_topc('#skF_2')=D_41 | g1_pre_topc(C_43, D_41)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_125])).
% 3.92/1.67  tff(c_257, plain, (![D_41, C_43]: (u1_pre_topc('#skF_2')=D_41 | g1_pre_topc(C_43, D_41)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_133])).
% 3.92/1.67  tff(c_258, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_257])).
% 3.92/1.67  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_258])).
% 3.92/1.67  tff(c_309, plain, (![D_61, C_62]: (u1_pre_topc('#skF_2')=D_61 | g1_pre_topc(C_62, D_61)!='#skF_3')), inference(splitRight, [status(thm)], [c_257])).
% 3.92/1.67  tff(c_351, plain, (![A_65]: (u1_pre_topc(A_65)=u1_pre_topc('#skF_2') | A_65!='#skF_3' | ~v1_pre_topc(A_65) | ~l1_pre_topc(A_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_309])).
% 3.92/1.67  tff(c_354, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_351])).
% 3.92/1.67  tff(c_360, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_354])).
% 3.92/1.67  tff(c_196, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_26])).
% 3.92/1.67  tff(c_374, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_196])).
% 3.92/1.67  tff(c_461, plain, (![C_71, A_72]: (m1_pre_topc(C_71, A_72) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_71), u1_pre_topc(C_71)), A_72) | ~l1_pre_topc(C_71) | ~v2_pre_topc(C_71) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_71), u1_pre_topc(C_71))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_71), u1_pre_topc(C_71))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.92/1.67  tff(c_473, plain, (![A_72]: (m1_pre_topc('#skF_2', A_72) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_72) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_72))), inference(superposition, [status(thm), theory('equality')], [c_191, c_461])).
% 3.92/1.67  tff(c_483, plain, (![A_72]: (m1_pre_topc('#skF_2', A_72) | ~m1_pre_topc('#skF_3', A_72) | ~l1_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_374, c_360, c_191, c_28, c_374, c_360, c_191, c_34, c_32, c_374, c_360, c_473])).
% 3.92/1.67  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_56, plain, (v1_borsuk_1('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_57, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 3.92/1.67  tff(c_24, plain, (![B_26, A_24]: (m1_subset_1(u1_struct_0(B_26), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.92/1.67  tff(c_229, plain, (![B_53, A_54]: (v4_pre_topc(u1_struct_0(B_53), A_54) | ~v1_borsuk_1(B_53, A_54) | ~m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.92/1.67  tff(c_242, plain, (![B_26, A_24]: (v4_pre_topc(u1_struct_0(B_26), A_24) | ~v1_borsuk_1(B_26, A_24) | ~v2_pre_topc(A_24) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_24, c_229])).
% 3.92/1.67  tff(c_295, plain, (![B_59, A_60]: (v1_borsuk_1(B_59, A_60) | ~v4_pre_topc(u1_struct_0(B_59), A_60) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.92/1.67  tff(c_525, plain, (![B_76, A_77]: (v1_borsuk_1(B_76, A_77) | ~v4_pre_topc(u1_struct_0(B_76), A_77) | ~v2_pre_topc(A_77) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_24, c_295])).
% 3.92/1.67  tff(c_564, plain, (![A_82]: (v1_borsuk_1('#skF_2', A_82) | ~v4_pre_topc(u1_struct_0('#skF_3'), A_82) | ~v2_pre_topc(A_82) | ~m1_pre_topc('#skF_2', A_82) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_191, c_525])).
% 3.92/1.67  tff(c_726, plain, (![A_95]: (v1_borsuk_1('#skF_2', A_95) | ~m1_pre_topc('#skF_2', A_95) | ~v1_borsuk_1('#skF_3', A_95) | ~v2_pre_topc(A_95) | ~m1_pre_topc('#skF_3', A_95) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_242, c_564])).
% 3.92/1.67  tff(c_40, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_96, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_59, c_40])).
% 3.92/1.67  tff(c_97, plain, (~v1_borsuk_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_96])).
% 3.92/1.67  tff(c_729, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_726, c_97])).
% 3.92/1.67  tff(c_732, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_38, c_57, c_729])).
% 3.92/1.67  tff(c_735, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_483, c_732])).
% 3.92/1.67  tff(c_739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_735])).
% 3.92/1.67  tff(c_740, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_96])).
% 3.92/1.67  tff(c_1056, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1050, c_740])).
% 3.92/1.67  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_1056])).
% 3.92/1.67  tff(c_1065, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.92/1.67  tff(c_1064, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.92/1.67  tff(c_1072, plain, (![A_127]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_127), u1_pre_topc(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.67  tff(c_1075, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1072])).
% 3.92/1.67  tff(c_1077, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1075])).
% 3.92/1.67  tff(c_1158, plain, (![D_140, B_141, C_142, A_143]: (D_140=B_141 | g1_pre_topc(C_142, D_140)!=g1_pre_topc(A_143, B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(k1_zfmisc_1(A_143))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_1216, plain, (![B_144, A_145]: (u1_pre_topc('#skF_2')=B_144 | g1_pre_topc(A_145, B_144)!='#skF_3' | ~m1_subset_1(B_144, k1_zfmisc_1(k1_zfmisc_1(A_145))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1158])).
% 3.92/1.67  tff(c_1264, plain, (![A_150]: (u1_pre_topc(A_150)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_150), u1_pre_topc(A_150))!='#skF_3' | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_4, c_1216])).
% 3.92/1.67  tff(c_1275, plain, (![A_151]: (u1_pre_topc(A_151)=u1_pre_topc('#skF_2') | A_151!='#skF_3' | ~l1_pre_topc(A_151) | ~v1_pre_topc(A_151) | ~l1_pre_topc(A_151))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1264])).
% 3.92/1.67  tff(c_1278, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1077, c_1275])).
% 3.92/1.67  tff(c_1284, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1278])).
% 3.92/1.67  tff(c_1117, plain, (![C_132, A_133, D_134, B_135]: (C_132=A_133 | g1_pre_topc(C_132, D_134)!=g1_pre_topc(A_133, B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(k1_zfmisc_1(A_133))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_1126, plain, (![A_136, B_137]: (u1_struct_0('#skF_2')=A_136 | g1_pre_topc(A_136, B_137)!='#skF_3' | ~m1_subset_1(B_137, k1_zfmisc_1(k1_zfmisc_1(A_136))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1117])).
% 3.92/1.67  tff(c_1131, plain, (![A_138]: (u1_struct_0(A_138)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_138), u1_pre_topc(A_138))!='#skF_3' | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_4, c_1126])).
% 3.92/1.67  tff(c_1143, plain, (![A_139]: (u1_struct_0(A_139)=u1_struct_0('#skF_2') | A_139!='#skF_3' | ~l1_pre_topc(A_139) | ~v1_pre_topc(A_139) | ~l1_pre_topc(A_139))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1131])).
% 3.92/1.67  tff(c_1146, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1077, c_1143])).
% 3.92/1.67  tff(c_1152, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1146])).
% 3.92/1.67  tff(c_1170, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_26])).
% 3.92/1.67  tff(c_1300, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1170])).
% 3.92/1.67  tff(c_1464, plain, (![C_166, A_167]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_166), u1_pre_topc(C_166)), A_167) | ~m1_pre_topc(C_166, A_167) | ~l1_pre_topc(C_166) | ~v2_pre_topc(C_166) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_166), u1_pre_topc(C_166))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_166), u1_pre_topc(C_166))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.92/1.67  tff(c_1473, plain, (![A_167]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3')), A_167) | ~m1_pre_topc('#skF_2', A_167) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_167))), inference(superposition, [status(thm), theory('equality')], [c_1284, c_1464])).
% 3.92/1.67  tff(c_1487, plain, (![A_168]: (m1_pre_topc('#skF_3', A_168) | ~m1_pre_topc('#skF_2', A_168) | ~l1_pre_topc(A_168))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1300, c_1284, c_1152, c_28, c_1300, c_1284, c_1152, c_34, c_32, c_1300, c_1152, c_1473])).
% 3.92/1.67  tff(c_1493, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1064, c_1487])).
% 3.92/1.67  tff(c_1497, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1493])).
% 3.92/1.67  tff(c_1499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1065, c_1497])).
% 3.92/1.67  tff(c_1501, plain, (~v1_borsuk_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 3.92/1.67  tff(c_54, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.92/1.67  tff(c_1502, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1501, c_54])).
% 3.92/1.67  tff(c_1529, plain, (![A_171]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_171), u1_pre_topc(A_171))) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.92/1.67  tff(c_1535, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1529])).
% 3.92/1.67  tff(c_1537, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1535])).
% 3.92/1.67  tff(c_1555, plain, (![C_175, A_176, D_177, B_178]: (C_175=A_176 | g1_pre_topc(C_175, D_177)!=g1_pre_topc(A_176, B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(k1_zfmisc_1(A_176))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_1563, plain, (![C_175, D_177]: (u1_struct_0('#skF_2')=C_175 | g1_pre_topc(C_175, D_177)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1555])).
% 3.92/1.67  tff(c_1609, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1563])).
% 3.92/1.67  tff(c_1612, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_1609])).
% 3.92/1.67  tff(c_1616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1612])).
% 3.92/1.67  tff(c_1619, plain, (![C_189, D_190]: (u1_struct_0('#skF_2')=C_189 | g1_pre_topc(C_189, D_190)!='#skF_3')), inference(splitRight, [status(thm)], [c_1563])).
% 3.92/1.67  tff(c_1636, plain, (![A_191]: (u1_struct_0(A_191)=u1_struct_0('#skF_2') | A_191!='#skF_3' | ~v1_pre_topc(A_191) | ~l1_pre_topc(A_191))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1619])).
% 3.92/1.67  tff(c_1639, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1537, c_1636])).
% 3.92/1.67  tff(c_1645, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1639])).
% 3.92/1.67  tff(c_1618, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1563])).
% 3.92/1.67  tff(c_1648, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1618])).
% 3.92/1.67  tff(c_1573, plain, (![D_181, B_182, C_183, A_184]: (D_181=B_182 | g1_pre_topc(C_183, D_181)!=g1_pre_topc(A_184, B_182) | ~m1_subset_1(B_182, k1_zfmisc_1(k1_zfmisc_1(A_184))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.67  tff(c_1581, plain, (![D_181, C_183]: (u1_pre_topc('#skF_2')=D_181 | g1_pre_topc(C_183, D_181)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1573])).
% 3.92/1.67  tff(c_1717, plain, (![D_181, C_183]: (u1_pre_topc('#skF_2')=D_181 | g1_pre_topc(C_183, D_181)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1581])).
% 3.92/1.67  tff(c_1718, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1717])).
% 3.92/1.67  tff(c_1736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1648, c_1718])).
% 3.92/1.67  tff(c_1769, plain, (![D_200, C_201]: (u1_pre_topc('#skF_2')=D_200 | g1_pre_topc(C_201, D_200)!='#skF_3')), inference(splitRight, [status(thm)], [c_1717])).
% 3.92/1.67  tff(c_1811, plain, (![A_204]: (u1_pre_topc(A_204)=u1_pre_topc('#skF_2') | A_204!='#skF_3' | ~v1_pre_topc(A_204) | ~l1_pre_topc(A_204))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1769])).
% 3.92/1.67  tff(c_1814, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1537, c_1811])).
% 3.92/1.67  tff(c_1820, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1814])).
% 3.92/1.67  tff(c_1650, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_26])).
% 3.92/1.67  tff(c_1834, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_1650])).
% 3.92/1.67  tff(c_1928, plain, (![C_210, A_211]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_210), u1_pre_topc(C_210)), A_211) | ~m1_pre_topc(C_210, A_211) | ~l1_pre_topc(C_210) | ~v2_pre_topc(C_210) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_210), u1_pre_topc(C_210))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_210), u1_pre_topc(C_210))) | ~l1_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.92/1.67  tff(c_1940, plain, (![A_211]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_211) | ~m1_pre_topc('#skF_2', A_211) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_211))), inference(superposition, [status(thm), theory('equality')], [c_1645, c_1928])).
% 3.92/1.67  tff(c_1951, plain, (![A_212]: (m1_pre_topc('#skF_3', A_212) | ~m1_pre_topc('#skF_2', A_212) | ~l1_pre_topc(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1834, c_1820, c_1645, c_28, c_1834, c_1820, c_1645, c_34, c_32, c_1834, c_1820, c_1940])).
% 3.92/1.67  tff(c_1957, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1502, c_1951])).
% 3.92/1.67  tff(c_1961, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1957])).
% 3.92/1.67  tff(c_1500, plain, (v1_borsuk_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 3.92/1.67  tff(c_1755, plain, (![B_198, A_199]: (v4_pre_topc(u1_struct_0(B_198), A_199) | ~v1_borsuk_1(B_198, A_199) | ~m1_subset_1(u1_struct_0(B_198), k1_zfmisc_1(u1_struct_0(A_199))) | ~m1_pre_topc(B_198, A_199) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.92/1.67  tff(c_1991, plain, (![B_215, A_216]: (v4_pre_topc(u1_struct_0(B_215), A_216) | ~v1_borsuk_1(B_215, A_216) | ~v2_pre_topc(A_216) | ~m1_pre_topc(B_215, A_216) | ~l1_pre_topc(A_216))), inference(resolution, [status(thm)], [c_24, c_1755])).
% 3.92/1.67  tff(c_2032, plain, (![A_221]: (v4_pre_topc(u1_struct_0('#skF_3'), A_221) | ~v1_borsuk_1('#skF_2', A_221) | ~v2_pre_topc(A_221) | ~m1_pre_topc('#skF_2', A_221) | ~l1_pre_topc(A_221))), inference(superposition, [status(thm), theory('equality')], [c_1645, c_1991])).
% 3.92/1.67  tff(c_1689, plain, (![B_192, A_193]: (v1_borsuk_1(B_192, A_193) | ~v4_pre_topc(u1_struct_0(B_192), A_193) | ~m1_subset_1(u1_struct_0(B_192), k1_zfmisc_1(u1_struct_0(A_193))) | ~m1_pre_topc(B_192, A_193) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.92/1.67  tff(c_1702, plain, (![B_26, A_24]: (v1_borsuk_1(B_26, A_24) | ~v4_pre_topc(u1_struct_0(B_26), A_24) | ~v2_pre_topc(A_24) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_24, c_1689])).
% 3.92/1.67  tff(c_2192, plain, (![A_234]: (v1_borsuk_1('#skF_3', A_234) | ~m1_pre_topc('#skF_3', A_234) | ~v1_borsuk_1('#skF_2', A_234) | ~v2_pre_topc(A_234) | ~m1_pre_topc('#skF_2', A_234) | ~l1_pre_topc(A_234))), inference(resolution, [status(thm)], [c_2032, c_1702])).
% 3.92/1.67  tff(c_2195, plain, (v1_borsuk_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1500, c_2192])).
% 3.92/1.67  tff(c_2198, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1502, c_38, c_1961, c_2195])).
% 3.92/1.67  tff(c_2200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1501, c_2198])).
% 3.92/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.67  
% 3.92/1.67  Inference rules
% 3.92/1.67  ----------------------
% 3.92/1.67  #Ref     : 12
% 3.92/1.67  #Sup     : 438
% 3.92/1.67  #Fact    : 0
% 3.92/1.67  #Define  : 0
% 3.92/1.67  #Split   : 15
% 3.92/1.67  #Chain   : 0
% 3.92/1.67  #Close   : 0
% 3.92/1.67  
% 3.92/1.67  Ordering : KBO
% 3.92/1.67  
% 3.92/1.67  Simplification rules
% 3.92/1.67  ----------------------
% 3.92/1.67  #Subsume      : 110
% 3.92/1.67  #Demod        : 640
% 3.92/1.67  #Tautology    : 199
% 3.92/1.67  #SimpNegUnit  : 5
% 3.92/1.67  #BackRed      : 33
% 3.92/1.67  
% 3.92/1.67  #Partial instantiations: 0
% 3.92/1.67  #Strategies tried      : 1
% 3.92/1.67  
% 3.92/1.67  Timing (in seconds)
% 3.92/1.67  ----------------------
% 3.92/1.68  Preprocessing        : 0.32
% 3.92/1.68  Parsing              : 0.17
% 3.92/1.68  CNF conversion       : 0.02
% 3.92/1.68  Main loop            : 0.57
% 3.92/1.68  Inferencing          : 0.20
% 3.92/1.68  Reduction            : 0.19
% 3.92/1.68  Demodulation         : 0.13
% 3.92/1.68  BG Simplification    : 0.03
% 3.92/1.68  Subsumption          : 0.11
% 3.92/1.68  Abstraction          : 0.02
% 3.92/1.68  MUC search           : 0.00
% 3.92/1.68  Cooper               : 0.00
% 3.92/1.68  Total                : 0.94
% 3.92/1.68  Index Insertion      : 0.00
% 3.92/1.68  Index Deletion       : 0.00
% 3.92/1.68  Index Matching       : 0.00
% 3.92/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
