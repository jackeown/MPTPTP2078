%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:24 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  192 (1482 expanded)
%              Number of leaves         :   25 ( 522 expanded)
%              Depth                    :   19
%              Number of atoms          :  499 (6022 expanded)
%              Number of equality atoms :  146 (1259 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(f_121,negated_conjecture,(
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
                 => ( ( v1_tsep_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_tsep_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_54,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_55,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_97,plain,(
    ! [A_42] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_42),u1_pre_topc(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_105,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_103])).

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

tff(c_111,plain,(
    ! [C_45,A_46,D_47,B_48] :
      ( C_45 = A_46
      | g1_pre_topc(C_45,D_47) != g1_pre_topc(A_46,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_120,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0('#skF_2') = A_49
      | g1_pre_topc(A_49,B_50) != '#skF_3'
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_125,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_51),u1_pre_topc(A_51)) != '#skF_3'
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_137,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = u1_struct_0('#skF_2')
      | A_52 != '#skF_3'
      | ~ l1_pre_topc(A_52)
      | ~ v1_pre_topc(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_140,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_137])).

tff(c_146,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_119,plain,(
    ! [C_45,D_47] :
      ( u1_struct_0('#skF_2') = C_45
      | g1_pre_topc(C_45,D_47) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_148,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_195,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_148])).

tff(c_171,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_4])).

tff(c_183,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_171])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_183])).

tff(c_211,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_256,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_211])).

tff(c_215,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_24])).

tff(c_278,plain,(
    ! [D_60,B_61,C_62,A_63] :
      ( D_60 = B_61
      | g1_pre_topc(C_62,D_60) != g1_pre_topc(A_63,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_282,plain,(
    ! [D_60,C_62] :
      ( u1_pre_topc('#skF_2') = D_60
      | g1_pre_topc(C_62,D_60) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_278])).

tff(c_289,plain,(
    ! [D_64,C_65] :
      ( u1_pre_topc('#skF_2') = D_64
      | g1_pre_topc(C_65,D_64) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_282])).

tff(c_313,plain,(
    ! [A_67] :
      ( u1_pre_topc(A_67) = u1_pre_topc('#skF_2')
      | A_67 != '#skF_3'
      | ~ v1_pre_topc(A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_289])).

tff(c_316,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_313])).

tff(c_322,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_316])).

tff(c_327,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_215])).

tff(c_522,plain,(
    ! [D_83,B_84,C_85,A_86] :
      ( m1_pre_topc(D_83,B_84)
      | ~ m1_pre_topc(C_85,A_86)
      | g1_pre_topc(u1_struct_0(D_83),u1_pre_topc(D_83)) != g1_pre_topc(u1_struct_0(C_85),u1_pre_topc(C_85))
      | g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)) != g1_pre_topc(u1_struct_0(A_86),u1_pre_topc(A_86))
      | ~ l1_pre_topc(D_83)
      | ~ l1_pre_topc(C_85)
      | ~ l1_pre_topc(B_84)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_524,plain,(
    ! [D_83,B_84] :
      ( m1_pre_topc(D_83,B_84)
      | g1_pre_topc(u1_struct_0(D_83),u1_pre_topc(D_83)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_83)
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_84)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_522])).

tff(c_548,plain,(
    ! [D_88,B_89] :
      ( m1_pre_topc(D_88,B_89)
      | g1_pre_topc(u1_struct_0(D_88),u1_pre_topc(D_88)) != '#skF_3'
      | g1_pre_topc(u1_struct_0(B_89),u1_pre_topc(B_89)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_88)
      | ~ l1_pre_topc(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_327,c_524])).

tff(c_554,plain,(
    ! [B_89] :
      ( m1_pre_topc('#skF_2',B_89)
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) != '#skF_3'
      | g1_pre_topc(u1_struct_0(B_89),u1_pre_topc(B_89)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_548])).

tff(c_563,plain,(
    ! [B_89] :
      ( m1_pre_topc('#skF_2',B_89)
      | g1_pre_topc(u1_struct_0(B_89),u1_pre_topc(B_89)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_327,c_322,c_554])).

tff(c_648,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_563])).

tff(c_650,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_648])).

tff(c_22,plain,(
    ! [B_34,A_32] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_392,plain,(
    ! [B_68,A_69] :
      ( v3_pre_topc(u1_struct_0(B_68),A_69)
      | ~ v1_tsep_1(B_68,A_69)
      | ~ m1_subset_1(u1_struct_0(B_68),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_411,plain,(
    ! [B_34,A_32] :
      ( v3_pre_topc(u1_struct_0(B_34),A_32)
      | ~ v1_tsep_1(B_34,A_32)
      | ~ v2_pre_topc(A_32)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_22,c_392])).

tff(c_447,plain,(
    ! [B_74,A_75] :
      ( v1_tsep_1(B_74,A_75)
      | ~ v3_pre_topc(u1_struct_0(B_74),A_75)
      | ~ m1_subset_1(u1_struct_0(B_74),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_496,plain,(
    ! [B_80,A_81] :
      ( v1_tsep_1(B_80,A_81)
      | ~ v3_pre_topc(u1_struct_0(B_80),A_81)
      | ~ v2_pre_topc(A_81)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_22,c_447])).

tff(c_528,plain,(
    ! [A_87] :
      ( v1_tsep_1('#skF_2',A_87)
      | ~ v3_pre_topc(u1_struct_0('#skF_3'),A_87)
      | ~ v2_pre_topc(A_87)
      | ~ m1_pre_topc('#skF_2',A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_496])).

tff(c_833,plain,(
    ! [A_112] :
      ( v1_tsep_1('#skF_2',A_112)
      | ~ m1_pre_topc('#skF_2',A_112)
      | ~ v1_tsep_1('#skF_3',A_112)
      | ~ v2_pre_topc(A_112)
      | ~ m1_pre_topc('#skF_3',A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_411,c_528])).

tff(c_38,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_86,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_56,c_38])).

tff(c_87,plain,(
    ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_839,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_833,c_87])).

tff(c_844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_56,c_36,c_55,c_650,c_839])).

tff(c_845,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_856,plain,(
    ! [A_114] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_114),u1_pre_topc(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_862,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_856])).

tff(c_864,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_862])).

tff(c_870,plain,(
    ! [C_117,A_118,D_119,B_120] :
      ( C_117 = A_118
      | g1_pre_topc(C_117,D_119) != g1_pre_topc(A_118,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k1_zfmisc_1(A_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_879,plain,(
    ! [A_121,B_122] :
      ( u1_struct_0('#skF_2') = A_121
      | g1_pre_topc(A_121,B_122) != '#skF_3'
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k1_zfmisc_1(A_121))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_870])).

tff(c_884,plain,(
    ! [A_123] :
      ( u1_struct_0(A_123) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_123),u1_pre_topc(A_123)) != '#skF_3'
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_4,c_879])).

tff(c_896,plain,(
    ! [A_124] :
      ( u1_struct_0(A_124) = u1_struct_0('#skF_2')
      | A_124 != '#skF_3'
      | ~ l1_pre_topc(A_124)
      | ~ v1_pre_topc(A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_884])).

tff(c_899,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_864,c_896])).

tff(c_905,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_899])).

tff(c_878,plain,(
    ! [C_117,D_119] :
      ( u1_struct_0('#skF_2') = C_117
      | g1_pre_topc(C_117,D_119) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_870])).

tff(c_907,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_878])).

tff(c_954,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_907])).

tff(c_930,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_4])).

tff(c_942,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_930])).

tff(c_968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_942])).

tff(c_970,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_1015,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_970])).

tff(c_974,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_24])).

tff(c_1037,plain,(
    ! [D_132,B_133,C_134,A_135] :
      ( D_132 = B_133
      | g1_pre_topc(C_134,D_132) != g1_pre_topc(A_135,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k1_zfmisc_1(A_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1041,plain,(
    ! [D_132,C_134] :
      ( u1_pre_topc('#skF_2') = D_132
      | g1_pre_topc(C_134,D_132) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_1037])).

tff(c_1048,plain,(
    ! [D_136,C_137] :
      ( u1_pre_topc('#skF_2') = D_136
      | g1_pre_topc(C_137,D_136) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1041])).

tff(c_1072,plain,(
    ! [A_139] :
      ( u1_pre_topc(A_139) = u1_pre_topc('#skF_2')
      | A_139 != '#skF_3'
      | ~ v1_pre_topc(A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1048])).

tff(c_1075,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_864,c_1072])).

tff(c_1081,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1075])).

tff(c_1086,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_974])).

tff(c_1281,plain,(
    ! [D_155,B_156,C_157,A_158] :
      ( m1_pre_topc(D_155,B_156)
      | ~ m1_pre_topc(C_157,A_158)
      | g1_pre_topc(u1_struct_0(D_155),u1_pre_topc(D_155)) != g1_pre_topc(u1_struct_0(C_157),u1_pre_topc(C_157))
      | g1_pre_topc(u1_struct_0(B_156),u1_pre_topc(B_156)) != g1_pre_topc(u1_struct_0(A_158),u1_pre_topc(A_158))
      | ~ l1_pre_topc(D_155)
      | ~ l1_pre_topc(C_157)
      | ~ l1_pre_topc(B_156)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1283,plain,(
    ! [D_155,B_156] :
      ( m1_pre_topc(D_155,B_156)
      | g1_pre_topc(u1_struct_0(D_155),u1_pre_topc(D_155)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | g1_pre_topc(u1_struct_0(B_156),u1_pre_topc(B_156)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_155)
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_156)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_1281])).

tff(c_1307,plain,(
    ! [D_160,B_161] :
      ( m1_pre_topc(D_160,B_161)
      | g1_pre_topc(u1_struct_0(D_160),u1_pre_topc(D_160)) != '#skF_3'
      | g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_160)
      | ~ l1_pre_topc(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_1086,c_1283])).

tff(c_1313,plain,(
    ! [B_161] :
      ( m1_pre_topc('#skF_2',B_161)
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) != '#skF_3'
      | g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_1307])).

tff(c_1322,plain,(
    ! [B_161] :
      ( m1_pre_topc('#skF_2',B_161)
      | g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1086,c_1081,c_1313])).

tff(c_1413,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1322])).

tff(c_1415,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1413])).

tff(c_1417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_845,c_1415])).

tff(c_1419,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1435,plain,(
    ! [A_171] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_171),u1_pre_topc(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1438,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1435])).

tff(c_1440,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1438])).

tff(c_1472,plain,(
    ! [C_175,A_176,D_177,B_178] :
      ( C_175 = A_176
      | g1_pre_topc(C_175,D_177) != g1_pre_topc(A_176,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(k1_zfmisc_1(A_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1481,plain,(
    ! [A_179,B_180] :
      ( u1_struct_0('#skF_2') = A_179
      | g1_pre_topc(A_179,B_180) != '#skF_3'
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k1_zfmisc_1(A_179))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1472])).

tff(c_1486,plain,(
    ! [A_181] :
      ( u1_struct_0(A_181) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_181),u1_pre_topc(A_181)) != '#skF_3'
      | ~ l1_pre_topc(A_181) ) ),
    inference(resolution,[status(thm)],[c_4,c_1481])).

tff(c_1498,plain,(
    ! [A_182] :
      ( u1_struct_0(A_182) = u1_struct_0('#skF_2')
      | A_182 != '#skF_3'
      | ~ l1_pre_topc(A_182)
      | ~ v1_pre_topc(A_182)
      | ~ l1_pre_topc(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1486])).

tff(c_1501,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1440,c_1498])).

tff(c_1507,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1501])).

tff(c_1512,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_24])).

tff(c_1557,plain,(
    ! [D_183,B_184,C_185,A_186] :
      ( D_183 = B_184
      | g1_pre_topc(C_185,D_183) != g1_pre_topc(A_186,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k1_zfmisc_1(A_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1627,plain,(
    ! [B_194,A_195] :
      ( u1_pre_topc('#skF_2') = B_194
      | g1_pre_topc(A_195,B_194) != '#skF_3'
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k1_zfmisc_1(A_195))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1512,c_1557])).

tff(c_1639,plain,(
    ! [A_196] :
      ( u1_pre_topc(A_196) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_196),u1_pre_topc(A_196)) != '#skF_3'
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_4,c_1627])).

tff(c_1650,plain,(
    ! [A_197] :
      ( u1_pre_topc(A_197) = u1_pre_topc('#skF_2')
      | A_197 != '#skF_3'
      | ~ l1_pre_topc(A_197)
      | ~ v1_pre_topc(A_197)
      | ~ l1_pre_topc(A_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1639])).

tff(c_1653,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1440,c_1650])).

tff(c_1659,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1653])).

tff(c_1665,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_1512])).

tff(c_1418,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1804,plain,(
    ! [D_204,B_205,C_206,A_207] :
      ( m1_pre_topc(D_204,B_205)
      | ~ m1_pre_topc(C_206,A_207)
      | g1_pre_topc(u1_struct_0(D_204),u1_pre_topc(D_204)) != g1_pre_topc(u1_struct_0(C_206),u1_pre_topc(C_206))
      | g1_pre_topc(u1_struct_0(B_205),u1_pre_topc(B_205)) != g1_pre_topc(u1_struct_0(A_207),u1_pre_topc(A_207))
      | ~ l1_pre_topc(D_204)
      | ~ l1_pre_topc(C_206)
      | ~ l1_pre_topc(B_205)
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1806,plain,(
    ! [D_204,B_205] :
      ( m1_pre_topc(D_204,B_205)
      | g1_pre_topc(u1_struct_0(D_204),u1_pre_topc(D_204)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(B_205),u1_pre_topc(B_205)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_204)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_205)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1418,c_1804])).

tff(c_1916,plain,(
    ! [D_222,B_223] :
      ( m1_pre_topc(D_222,B_223)
      | g1_pre_topc(u1_struct_0(D_222),u1_pre_topc(D_222)) != '#skF_3'
      | g1_pre_topc(u1_struct_0(B_223),u1_pre_topc(B_223)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_222)
      | ~ l1_pre_topc(B_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1665,c_1659,c_1507,c_1806])).

tff(c_1918,plain,(
    ! [B_223] :
      ( m1_pre_topc('#skF_3',B_223)
      | g1_pre_topc(u1_struct_0(B_223),u1_pre_topc(B_223)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1665,c_1916])).

tff(c_1927,plain,(
    ! [B_223] :
      ( m1_pre_topc('#skF_3',B_223)
      | g1_pre_topc(u1_struct_0(B_223),u1_pre_topc(B_223)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1918])).

tff(c_1934,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1927])).

tff(c_1936,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1934])).

tff(c_1938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1419,c_1936])).

tff(c_1940,plain,(
    ~ v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1946,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1940,c_52])).

tff(c_1941,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1939,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1957,plain,(
    ! [A_226] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_226),u1_pre_topc(A_226)))
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1960,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1957])).

tff(c_1962,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1960])).

tff(c_1994,plain,(
    ! [C_230,A_231,D_232,B_233] :
      ( C_230 = A_231
      | g1_pre_topc(C_230,D_232) != g1_pre_topc(A_231,B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(k1_zfmisc_1(A_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2003,plain,(
    ! [A_234,B_235] :
      ( u1_struct_0('#skF_2') = A_234
      | g1_pre_topc(A_234,B_235) != '#skF_3'
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k1_zfmisc_1(A_234))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1994])).

tff(c_2008,plain,(
    ! [A_236] :
      ( u1_struct_0(A_236) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_236),u1_pre_topc(A_236)) != '#skF_3'
      | ~ l1_pre_topc(A_236) ) ),
    inference(resolution,[status(thm)],[c_4,c_2003])).

tff(c_2020,plain,(
    ! [A_237] :
      ( u1_struct_0(A_237) = u1_struct_0('#skF_2')
      | A_237 != '#skF_3'
      | ~ l1_pre_topc(A_237)
      | ~ v1_pre_topc(A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2008])).

tff(c_2023,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1962,c_2020])).

tff(c_2029,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2023])).

tff(c_2125,plain,(
    ! [B_247,A_248] :
      ( v3_pre_topc(u1_struct_0(B_247),A_248)
      | ~ v1_tsep_1(B_247,A_248)
      | ~ m1_subset_1(u1_struct_0(B_247),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_pre_topc(B_247,A_248)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2383,plain,(
    ! [B_270,A_271] :
      ( v3_pre_topc(u1_struct_0(B_270),A_271)
      | ~ v1_tsep_1(B_270,A_271)
      | ~ v2_pre_topc(A_271)
      | ~ m1_pre_topc(B_270,A_271)
      | ~ l1_pre_topc(A_271) ) ),
    inference(resolution,[status(thm)],[c_22,c_2125])).

tff(c_2411,plain,(
    ! [A_273] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),A_273)
      | ~ v1_tsep_1('#skF_2',A_273)
      | ~ v2_pre_topc(A_273)
      | ~ m1_pre_topc('#skF_2',A_273)
      | ~ l1_pre_topc(A_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2029,c_2383])).

tff(c_2251,plain,(
    ! [B_253,A_254] :
      ( v1_tsep_1(B_253,A_254)
      | ~ v3_pre_topc(u1_struct_0(B_253),A_254)
      | ~ m1_subset_1(u1_struct_0(B_253),k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ m1_pre_topc(B_253,A_254)
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2274,plain,(
    ! [B_34,A_32] :
      ( v1_tsep_1(B_34,A_32)
      | ~ v3_pre_topc(u1_struct_0(B_34),A_32)
      | ~ v2_pre_topc(A_32)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_22,c_2251])).

tff(c_2689,plain,(
    ! [A_296] :
      ( v1_tsep_1('#skF_3',A_296)
      | ~ m1_pre_topc('#skF_3',A_296)
      | ~ v1_tsep_1('#skF_2',A_296)
      | ~ v2_pre_topc(A_296)
      | ~ m1_pre_topc('#skF_2',A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(resolution,[status(thm)],[c_2411,c_2274])).

tff(c_2692,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1939,c_2689])).

tff(c_2695,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1946,c_36,c_1941,c_2692])).

tff(c_2697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1940,c_2695])).

tff(c_2699,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2717,plain,(
    ! [A_299] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_299),u1_pre_topc(A_299)))
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2720,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2717])).

tff(c_2722,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2720])).

tff(c_2754,plain,(
    ! [C_303,A_304,D_305,B_306] :
      ( C_303 = A_304
      | g1_pre_topc(C_303,D_305) != g1_pre_topc(A_304,B_306)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k1_zfmisc_1(A_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2763,plain,(
    ! [A_307,B_308] :
      ( u1_struct_0('#skF_2') = A_307
      | g1_pre_topc(A_307,B_308) != '#skF_3'
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k1_zfmisc_1(A_307))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2754])).

tff(c_2768,plain,(
    ! [A_309] :
      ( u1_struct_0(A_309) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_309),u1_pre_topc(A_309)) != '#skF_3'
      | ~ l1_pre_topc(A_309) ) ),
    inference(resolution,[status(thm)],[c_4,c_2763])).

tff(c_2780,plain,(
    ! [A_310] :
      ( u1_struct_0(A_310) = u1_struct_0('#skF_2')
      | A_310 != '#skF_3'
      | ~ l1_pre_topc(A_310)
      | ~ v1_pre_topc(A_310)
      | ~ l1_pre_topc(A_310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2768])).

tff(c_2783,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2722,c_2780])).

tff(c_2789,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2783])).

tff(c_2794,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2789,c_24])).

tff(c_2839,plain,(
    ! [D_311,B_312,C_313,A_314] :
      ( D_311 = B_312
      | g1_pre_topc(C_313,D_311) != g1_pre_topc(A_314,B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k1_zfmisc_1(A_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2909,plain,(
    ! [B_322,A_323] :
      ( u1_pre_topc('#skF_2') = B_322
      | g1_pre_topc(A_323,B_322) != '#skF_3'
      | ~ m1_subset_1(B_322,k1_zfmisc_1(k1_zfmisc_1(A_323))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2794,c_2839])).

tff(c_2921,plain,(
    ! [A_324] :
      ( u1_pre_topc(A_324) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_324),u1_pre_topc(A_324)) != '#skF_3'
      | ~ l1_pre_topc(A_324) ) ),
    inference(resolution,[status(thm)],[c_4,c_2909])).

tff(c_2932,plain,(
    ! [A_325] :
      ( u1_pre_topc(A_325) = u1_pre_topc('#skF_2')
      | A_325 != '#skF_3'
      | ~ l1_pre_topc(A_325)
      | ~ v1_pre_topc(A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2921])).

tff(c_2935,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2722,c_2932])).

tff(c_2941,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2935])).

tff(c_2947,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_2794])).

tff(c_2698,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3086,plain,(
    ! [D_332,B_333,C_334,A_335] :
      ( m1_pre_topc(D_332,B_333)
      | ~ m1_pre_topc(C_334,A_335)
      | g1_pre_topc(u1_struct_0(D_332),u1_pre_topc(D_332)) != g1_pre_topc(u1_struct_0(C_334),u1_pre_topc(C_334))
      | g1_pre_topc(u1_struct_0(B_333),u1_pre_topc(B_333)) != g1_pre_topc(u1_struct_0(A_335),u1_pre_topc(A_335))
      | ~ l1_pre_topc(D_332)
      | ~ l1_pre_topc(C_334)
      | ~ l1_pre_topc(B_333)
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3088,plain,(
    ! [D_332,B_333] :
      ( m1_pre_topc(D_332,B_333)
      | g1_pre_topc(u1_struct_0(D_332),u1_pre_topc(D_332)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(B_333),u1_pre_topc(B_333)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_332)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_333)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2698,c_3086])).

tff(c_3198,plain,(
    ! [D_350,B_351] :
      ( m1_pre_topc(D_350,B_351)
      | g1_pre_topc(u1_struct_0(D_350),u1_pre_topc(D_350)) != '#skF_3'
      | g1_pre_topc(u1_struct_0(B_351),u1_pre_topc(B_351)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_350)
      | ~ l1_pre_topc(B_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_2947,c_2941,c_2789,c_3088])).

tff(c_3200,plain,(
    ! [B_351] :
      ( m1_pre_topc('#skF_3',B_351)
      | g1_pre_topc(u1_struct_0(B_351),u1_pre_topc(B_351)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2947,c_3198])).

tff(c_3209,plain,(
    ! [B_351] :
      ( m1_pre_topc('#skF_3',B_351)
      | g1_pre_topc(u1_struct_0(B_351),u1_pre_topc(B_351)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3200])).

tff(c_3216,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3209])).

tff(c_3218,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3216])).

tff(c_3220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2699,c_3218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:10:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.79  
% 4.66/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.79  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.66/1.79  
% 4.66/1.79  %Foreground sorts:
% 4.66/1.79  
% 4.66/1.79  
% 4.66/1.79  %Background operators:
% 4.66/1.79  
% 4.66/1.79  
% 4.66/1.79  %Foreground operators:
% 4.66/1.79  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.66/1.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.66/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.79  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.66/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.66/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.66/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.66/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.79  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.66/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.66/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.66/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.66/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.79  
% 4.79/1.82  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 4.79/1.82  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 4.79/1.82  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.79/1.82  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.79/1.82  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.79/1.82  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_pre_topc)).
% 4.79/1.82  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.79/1.82  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.79/1.82  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_46, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_56, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.79/1.82  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_54, plain, (v1_tsep_1('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_55, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 4.79/1.82  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_26, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_24, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_97, plain, (![A_42]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_42), u1_pre_topc(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.79/1.82  tff(c_103, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_97])).
% 4.79/1.82  tff(c_105, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_103])).
% 4.79/1.82  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.79/1.82  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_pre_topc(A_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2)))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.79/1.82  tff(c_111, plain, (![C_45, A_46, D_47, B_48]: (C_45=A_46 | g1_pre_topc(C_45, D_47)!=g1_pre_topc(A_46, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_120, plain, (![A_49, B_50]: (u1_struct_0('#skF_2')=A_49 | g1_pre_topc(A_49, B_50)!='#skF_3' | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_111])).
% 4.79/1.82  tff(c_125, plain, (![A_51]: (u1_struct_0(A_51)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_51), u1_pre_topc(A_51))!='#skF_3' | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_4, c_120])).
% 4.79/1.82  tff(c_137, plain, (![A_52]: (u1_struct_0(A_52)=u1_struct_0('#skF_2') | A_52!='#skF_3' | ~l1_pre_topc(A_52) | ~v1_pre_topc(A_52) | ~l1_pre_topc(A_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_125])).
% 4.79/1.82  tff(c_140, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_105, c_137])).
% 4.79/1.82  tff(c_146, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_140])).
% 4.79/1.82  tff(c_119, plain, (![C_45, D_47]: (u1_struct_0('#skF_2')=C_45 | g1_pre_topc(C_45, D_47)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_111])).
% 4.79/1.82  tff(c_148, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_119])).
% 4.79/1.82  tff(c_195, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_148])).
% 4.79/1.82  tff(c_171, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_146, c_4])).
% 4.79/1.82  tff(c_183, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_171])).
% 4.79/1.82  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_183])).
% 4.79/1.82  tff(c_211, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_119])).
% 4.79/1.82  tff(c_256, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_211])).
% 4.79/1.82  tff(c_215, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_24])).
% 4.79/1.82  tff(c_278, plain, (![D_60, B_61, C_62, A_63]: (D_60=B_61 | g1_pre_topc(C_62, D_60)!=g1_pre_topc(A_63, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_282, plain, (![D_60, C_62]: (u1_pre_topc('#skF_2')=D_60 | g1_pre_topc(C_62, D_60)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_215, c_278])).
% 4.79/1.82  tff(c_289, plain, (![D_64, C_65]: (u1_pre_topc('#skF_2')=D_64 | g1_pre_topc(C_65, D_64)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_282])).
% 4.79/1.82  tff(c_313, plain, (![A_67]: (u1_pre_topc(A_67)=u1_pre_topc('#skF_2') | A_67!='#skF_3' | ~v1_pre_topc(A_67) | ~l1_pre_topc(A_67))), inference(superposition, [status(thm), theory('equality')], [c_2, c_289])).
% 4.79/1.82  tff(c_316, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_105, c_313])).
% 4.79/1.82  tff(c_322, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_316])).
% 4.79/1.82  tff(c_327, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_215])).
% 4.79/1.82  tff(c_522, plain, (![D_83, B_84, C_85, A_86]: (m1_pre_topc(D_83, B_84) | ~m1_pre_topc(C_85, A_86) | g1_pre_topc(u1_struct_0(D_83), u1_pre_topc(D_83))!=g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85)) | g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84))!=g1_pre_topc(u1_struct_0(A_86), u1_pre_topc(A_86)) | ~l1_pre_topc(D_83) | ~l1_pre_topc(C_85) | ~l1_pre_topc(B_84) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.79/1.82  tff(c_524, plain, (![D_83, B_84]: (m1_pre_topc(D_83, B_84) | g1_pre_topc(u1_struct_0(D_83), u1_pre_topc(D_83))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_83) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(B_84) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_522])).
% 4.79/1.82  tff(c_548, plain, (![D_88, B_89]: (m1_pre_topc(D_88, B_89) | g1_pre_topc(u1_struct_0(D_88), u1_pre_topc(D_88))!='#skF_3' | g1_pre_topc(u1_struct_0(B_89), u1_pre_topc(B_89))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_88) | ~l1_pre_topc(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_327, c_524])).
% 4.79/1.82  tff(c_554, plain, (![B_89]: (m1_pre_topc('#skF_2', B_89) | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))!='#skF_3' | g1_pre_topc(u1_struct_0(B_89), u1_pre_topc(B_89))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_89))), inference(superposition, [status(thm), theory('equality')], [c_146, c_548])).
% 4.79/1.82  tff(c_563, plain, (![B_89]: (m1_pre_topc('#skF_2', B_89) | g1_pre_topc(u1_struct_0(B_89), u1_pre_topc(B_89))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_327, c_322, c_554])).
% 4.79/1.82  tff(c_648, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_563])).
% 4.79/1.82  tff(c_650, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_648])).
% 4.79/1.82  tff(c_22, plain, (![B_34, A_32]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.79/1.82  tff(c_392, plain, (![B_68, A_69]: (v3_pre_topc(u1_struct_0(B_68), A_69) | ~v1_tsep_1(B_68, A_69) | ~m1_subset_1(u1_struct_0(B_68), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.79/1.82  tff(c_411, plain, (![B_34, A_32]: (v3_pre_topc(u1_struct_0(B_34), A_32) | ~v1_tsep_1(B_34, A_32) | ~v2_pre_topc(A_32) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_22, c_392])).
% 4.79/1.82  tff(c_447, plain, (![B_74, A_75]: (v1_tsep_1(B_74, A_75) | ~v3_pre_topc(u1_struct_0(B_74), A_75) | ~m1_subset_1(u1_struct_0(B_74), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.79/1.82  tff(c_496, plain, (![B_80, A_81]: (v1_tsep_1(B_80, A_81) | ~v3_pre_topc(u1_struct_0(B_80), A_81) | ~v2_pre_topc(A_81) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_22, c_447])).
% 4.79/1.82  tff(c_528, plain, (![A_87]: (v1_tsep_1('#skF_2', A_87) | ~v3_pre_topc(u1_struct_0('#skF_3'), A_87) | ~v2_pre_topc(A_87) | ~m1_pre_topc('#skF_2', A_87) | ~l1_pre_topc(A_87))), inference(superposition, [status(thm), theory('equality')], [c_146, c_496])).
% 4.79/1.82  tff(c_833, plain, (![A_112]: (v1_tsep_1('#skF_2', A_112) | ~m1_pre_topc('#skF_2', A_112) | ~v1_tsep_1('#skF_3', A_112) | ~v2_pre_topc(A_112) | ~m1_pre_topc('#skF_3', A_112) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_411, c_528])).
% 4.79/1.82  tff(c_38, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_86, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_56, c_38])).
% 4.79/1.82  tff(c_87, plain, (~v1_tsep_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_86])).
% 4.79/1.82  tff(c_839, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_833, c_87])).
% 4.79/1.82  tff(c_844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_56, c_36, c_55, c_650, c_839])).
% 4.79/1.82  tff(c_845, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_86])).
% 4.79/1.82  tff(c_856, plain, (![A_114]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_114), u1_pre_topc(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.79/1.82  tff(c_862, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_856])).
% 4.79/1.82  tff(c_864, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_862])).
% 4.79/1.82  tff(c_870, plain, (![C_117, A_118, D_119, B_120]: (C_117=A_118 | g1_pre_topc(C_117, D_119)!=g1_pre_topc(A_118, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(k1_zfmisc_1(A_118))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_879, plain, (![A_121, B_122]: (u1_struct_0('#skF_2')=A_121 | g1_pre_topc(A_121, B_122)!='#skF_3' | ~m1_subset_1(B_122, k1_zfmisc_1(k1_zfmisc_1(A_121))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_870])).
% 4.79/1.82  tff(c_884, plain, (![A_123]: (u1_struct_0(A_123)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_123), u1_pre_topc(A_123))!='#skF_3' | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_4, c_879])).
% 4.79/1.82  tff(c_896, plain, (![A_124]: (u1_struct_0(A_124)=u1_struct_0('#skF_2') | A_124!='#skF_3' | ~l1_pre_topc(A_124) | ~v1_pre_topc(A_124) | ~l1_pre_topc(A_124))), inference(superposition, [status(thm), theory('equality')], [c_2, c_884])).
% 4.79/1.82  tff(c_899, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_864, c_896])).
% 4.79/1.82  tff(c_905, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_899])).
% 4.79/1.82  tff(c_878, plain, (![C_117, D_119]: (u1_struct_0('#skF_2')=C_117 | g1_pre_topc(C_117, D_119)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_870])).
% 4.79/1.82  tff(c_907, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_878])).
% 4.79/1.82  tff(c_954, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_907])).
% 4.79/1.82  tff(c_930, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_905, c_4])).
% 4.79/1.82  tff(c_942, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_930])).
% 4.79/1.82  tff(c_968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_954, c_942])).
% 4.79/1.82  tff(c_970, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_878])).
% 4.79/1.82  tff(c_1015, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_905, c_970])).
% 4.79/1.82  tff(c_974, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_905, c_24])).
% 4.79/1.82  tff(c_1037, plain, (![D_132, B_133, C_134, A_135]: (D_132=B_133 | g1_pre_topc(C_134, D_132)!=g1_pre_topc(A_135, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(k1_zfmisc_1(A_135))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_1041, plain, (![D_132, C_134]: (u1_pre_topc('#skF_2')=D_132 | g1_pre_topc(C_134, D_132)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_974, c_1037])).
% 4.79/1.82  tff(c_1048, plain, (![D_136, C_137]: (u1_pre_topc('#skF_2')=D_136 | g1_pre_topc(C_137, D_136)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1041])).
% 4.79/1.82  tff(c_1072, plain, (![A_139]: (u1_pre_topc(A_139)=u1_pre_topc('#skF_2') | A_139!='#skF_3' | ~v1_pre_topc(A_139) | ~l1_pre_topc(A_139))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1048])).
% 4.79/1.82  tff(c_1075, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_864, c_1072])).
% 4.79/1.82  tff(c_1081, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1075])).
% 4.79/1.82  tff(c_1086, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_974])).
% 4.79/1.82  tff(c_1281, plain, (![D_155, B_156, C_157, A_158]: (m1_pre_topc(D_155, B_156) | ~m1_pre_topc(C_157, A_158) | g1_pre_topc(u1_struct_0(D_155), u1_pre_topc(D_155))!=g1_pre_topc(u1_struct_0(C_157), u1_pre_topc(C_157)) | g1_pre_topc(u1_struct_0(B_156), u1_pre_topc(B_156))!=g1_pre_topc(u1_struct_0(A_158), u1_pre_topc(A_158)) | ~l1_pre_topc(D_155) | ~l1_pre_topc(C_157) | ~l1_pre_topc(B_156) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.79/1.82  tff(c_1283, plain, (![D_155, B_156]: (m1_pre_topc(D_155, B_156) | g1_pre_topc(u1_struct_0(D_155), u1_pre_topc(D_155))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | g1_pre_topc(u1_struct_0(B_156), u1_pre_topc(B_156))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_155) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(B_156) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_1281])).
% 4.79/1.82  tff(c_1307, plain, (![D_160, B_161]: (m1_pre_topc(D_160, B_161) | g1_pre_topc(u1_struct_0(D_160), u1_pre_topc(D_160))!='#skF_3' | g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_160) | ~l1_pre_topc(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_1086, c_1283])).
% 4.79/1.82  tff(c_1313, plain, (![B_161]: (m1_pre_topc('#skF_2', B_161) | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))!='#skF_3' | g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_161))), inference(superposition, [status(thm), theory('equality')], [c_905, c_1307])).
% 4.79/1.82  tff(c_1322, plain, (![B_161]: (m1_pre_topc('#skF_2', B_161) | g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1086, c_1081, c_1313])).
% 4.79/1.82  tff(c_1413, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_1322])).
% 4.79/1.82  tff(c_1415, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1413])).
% 4.79/1.82  tff(c_1417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_845, c_1415])).
% 4.79/1.82  tff(c_1419, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.79/1.82  tff(c_1435, plain, (![A_171]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_171), u1_pre_topc(A_171))) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.79/1.82  tff(c_1438, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1435])).
% 4.79/1.82  tff(c_1440, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1438])).
% 4.79/1.82  tff(c_1472, plain, (![C_175, A_176, D_177, B_178]: (C_175=A_176 | g1_pre_topc(C_175, D_177)!=g1_pre_topc(A_176, B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(k1_zfmisc_1(A_176))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_1481, plain, (![A_179, B_180]: (u1_struct_0('#skF_2')=A_179 | g1_pre_topc(A_179, B_180)!='#skF_3' | ~m1_subset_1(B_180, k1_zfmisc_1(k1_zfmisc_1(A_179))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1472])).
% 4.79/1.82  tff(c_1486, plain, (![A_181]: (u1_struct_0(A_181)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_181), u1_pre_topc(A_181))!='#skF_3' | ~l1_pre_topc(A_181))), inference(resolution, [status(thm)], [c_4, c_1481])).
% 4.79/1.82  tff(c_1498, plain, (![A_182]: (u1_struct_0(A_182)=u1_struct_0('#skF_2') | A_182!='#skF_3' | ~l1_pre_topc(A_182) | ~v1_pre_topc(A_182) | ~l1_pre_topc(A_182))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1486])).
% 4.79/1.82  tff(c_1501, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1440, c_1498])).
% 4.79/1.82  tff(c_1507, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1501])).
% 4.79/1.82  tff(c_1512, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_24])).
% 4.79/1.82  tff(c_1557, plain, (![D_183, B_184, C_185, A_186]: (D_183=B_184 | g1_pre_topc(C_185, D_183)!=g1_pre_topc(A_186, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(k1_zfmisc_1(A_186))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_1627, plain, (![B_194, A_195]: (u1_pre_topc('#skF_2')=B_194 | g1_pre_topc(A_195, B_194)!='#skF_3' | ~m1_subset_1(B_194, k1_zfmisc_1(k1_zfmisc_1(A_195))))), inference(superposition, [status(thm), theory('equality')], [c_1512, c_1557])).
% 4.79/1.82  tff(c_1639, plain, (![A_196]: (u1_pre_topc(A_196)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_196), u1_pre_topc(A_196))!='#skF_3' | ~l1_pre_topc(A_196))), inference(resolution, [status(thm)], [c_4, c_1627])).
% 4.79/1.82  tff(c_1650, plain, (![A_197]: (u1_pre_topc(A_197)=u1_pre_topc('#skF_2') | A_197!='#skF_3' | ~l1_pre_topc(A_197) | ~v1_pre_topc(A_197) | ~l1_pre_topc(A_197))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1639])).
% 4.79/1.82  tff(c_1653, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1440, c_1650])).
% 4.79/1.82  tff(c_1659, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1653])).
% 4.79/1.82  tff(c_1665, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1659, c_1512])).
% 4.79/1.82  tff(c_1418, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.79/1.82  tff(c_1804, plain, (![D_204, B_205, C_206, A_207]: (m1_pre_topc(D_204, B_205) | ~m1_pre_topc(C_206, A_207) | g1_pre_topc(u1_struct_0(D_204), u1_pre_topc(D_204))!=g1_pre_topc(u1_struct_0(C_206), u1_pre_topc(C_206)) | g1_pre_topc(u1_struct_0(B_205), u1_pre_topc(B_205))!=g1_pre_topc(u1_struct_0(A_207), u1_pre_topc(A_207)) | ~l1_pre_topc(D_204) | ~l1_pre_topc(C_206) | ~l1_pre_topc(B_205) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.79/1.82  tff(c_1806, plain, (![D_204, B_205]: (m1_pre_topc(D_204, B_205) | g1_pre_topc(u1_struct_0(D_204), u1_pre_topc(D_204))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(B_205), u1_pre_topc(B_205))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_204) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_205) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1418, c_1804])).
% 4.79/1.82  tff(c_1916, plain, (![D_222, B_223]: (m1_pre_topc(D_222, B_223) | g1_pre_topc(u1_struct_0(D_222), u1_pre_topc(D_222))!='#skF_3' | g1_pre_topc(u1_struct_0(B_223), u1_pre_topc(B_223))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_222) | ~l1_pre_topc(B_223))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1665, c_1659, c_1507, c_1806])).
% 4.79/1.82  tff(c_1918, plain, (![B_223]: (m1_pre_topc('#skF_3', B_223) | g1_pre_topc(u1_struct_0(B_223), u1_pre_topc(B_223))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(B_223))), inference(superposition, [status(thm), theory('equality')], [c_1665, c_1916])).
% 4.79/1.82  tff(c_1927, plain, (![B_223]: (m1_pre_topc('#skF_3', B_223) | g1_pre_topc(u1_struct_0(B_223), u1_pre_topc(B_223))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_223))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1918])).
% 4.79/1.82  tff(c_1934, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_1927])).
% 4.79/1.82  tff(c_1936, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1934])).
% 4.79/1.82  tff(c_1938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1419, c_1936])).
% 4.79/1.82  tff(c_1940, plain, (~v1_tsep_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 4.79/1.82  tff(c_52, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.79/1.82  tff(c_1946, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1940, c_52])).
% 4.79/1.82  tff(c_1941, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.79/1.82  tff(c_1939, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 4.79/1.82  tff(c_1957, plain, (![A_226]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_226), u1_pre_topc(A_226))) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.79/1.82  tff(c_1960, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1957])).
% 4.79/1.82  tff(c_1962, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1960])).
% 4.79/1.82  tff(c_1994, plain, (![C_230, A_231, D_232, B_233]: (C_230=A_231 | g1_pre_topc(C_230, D_232)!=g1_pre_topc(A_231, B_233) | ~m1_subset_1(B_233, k1_zfmisc_1(k1_zfmisc_1(A_231))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_2003, plain, (![A_234, B_235]: (u1_struct_0('#skF_2')=A_234 | g1_pre_topc(A_234, B_235)!='#skF_3' | ~m1_subset_1(B_235, k1_zfmisc_1(k1_zfmisc_1(A_234))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1994])).
% 4.79/1.82  tff(c_2008, plain, (![A_236]: (u1_struct_0(A_236)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_236), u1_pre_topc(A_236))!='#skF_3' | ~l1_pre_topc(A_236))), inference(resolution, [status(thm)], [c_4, c_2003])).
% 4.79/1.82  tff(c_2020, plain, (![A_237]: (u1_struct_0(A_237)=u1_struct_0('#skF_2') | A_237!='#skF_3' | ~l1_pre_topc(A_237) | ~v1_pre_topc(A_237) | ~l1_pre_topc(A_237))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2008])).
% 4.79/1.82  tff(c_2023, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1962, c_2020])).
% 4.79/1.82  tff(c_2029, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2023])).
% 4.79/1.82  tff(c_2125, plain, (![B_247, A_248]: (v3_pre_topc(u1_struct_0(B_247), A_248) | ~v1_tsep_1(B_247, A_248) | ~m1_subset_1(u1_struct_0(B_247), k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_pre_topc(B_247, A_248) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.79/1.82  tff(c_2383, plain, (![B_270, A_271]: (v3_pre_topc(u1_struct_0(B_270), A_271) | ~v1_tsep_1(B_270, A_271) | ~v2_pre_topc(A_271) | ~m1_pre_topc(B_270, A_271) | ~l1_pre_topc(A_271))), inference(resolution, [status(thm)], [c_22, c_2125])).
% 4.79/1.82  tff(c_2411, plain, (![A_273]: (v3_pre_topc(u1_struct_0('#skF_3'), A_273) | ~v1_tsep_1('#skF_2', A_273) | ~v2_pre_topc(A_273) | ~m1_pre_topc('#skF_2', A_273) | ~l1_pre_topc(A_273))), inference(superposition, [status(thm), theory('equality')], [c_2029, c_2383])).
% 4.79/1.82  tff(c_2251, plain, (![B_253, A_254]: (v1_tsep_1(B_253, A_254) | ~v3_pre_topc(u1_struct_0(B_253), A_254) | ~m1_subset_1(u1_struct_0(B_253), k1_zfmisc_1(u1_struct_0(A_254))) | ~m1_pre_topc(B_253, A_254) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.79/1.82  tff(c_2274, plain, (![B_34, A_32]: (v1_tsep_1(B_34, A_32) | ~v3_pre_topc(u1_struct_0(B_34), A_32) | ~v2_pre_topc(A_32) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_22, c_2251])).
% 4.79/1.82  tff(c_2689, plain, (![A_296]: (v1_tsep_1('#skF_3', A_296) | ~m1_pre_topc('#skF_3', A_296) | ~v1_tsep_1('#skF_2', A_296) | ~v2_pre_topc(A_296) | ~m1_pre_topc('#skF_2', A_296) | ~l1_pre_topc(A_296))), inference(resolution, [status(thm)], [c_2411, c_2274])).
% 4.79/1.82  tff(c_2692, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1939, c_2689])).
% 4.79/1.82  tff(c_2695, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1946, c_36, c_1941, c_2692])).
% 4.79/1.82  tff(c_2697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1940, c_2695])).
% 4.79/1.82  tff(c_2699, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.79/1.82  tff(c_2717, plain, (![A_299]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_299), u1_pre_topc(A_299))) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.79/1.82  tff(c_2720, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2717])).
% 4.79/1.82  tff(c_2722, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2720])).
% 4.79/1.82  tff(c_2754, plain, (![C_303, A_304, D_305, B_306]: (C_303=A_304 | g1_pre_topc(C_303, D_305)!=g1_pre_topc(A_304, B_306) | ~m1_subset_1(B_306, k1_zfmisc_1(k1_zfmisc_1(A_304))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_2763, plain, (![A_307, B_308]: (u1_struct_0('#skF_2')=A_307 | g1_pre_topc(A_307, B_308)!='#skF_3' | ~m1_subset_1(B_308, k1_zfmisc_1(k1_zfmisc_1(A_307))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2754])).
% 4.79/1.82  tff(c_2768, plain, (![A_309]: (u1_struct_0(A_309)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_309), u1_pre_topc(A_309))!='#skF_3' | ~l1_pre_topc(A_309))), inference(resolution, [status(thm)], [c_4, c_2763])).
% 4.79/1.82  tff(c_2780, plain, (![A_310]: (u1_struct_0(A_310)=u1_struct_0('#skF_2') | A_310!='#skF_3' | ~l1_pre_topc(A_310) | ~v1_pre_topc(A_310) | ~l1_pre_topc(A_310))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2768])).
% 4.79/1.82  tff(c_2783, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2722, c_2780])).
% 4.79/1.82  tff(c_2789, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2783])).
% 4.79/1.82  tff(c_2794, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2789, c_24])).
% 4.79/1.82  tff(c_2839, plain, (![D_311, B_312, C_313, A_314]: (D_311=B_312 | g1_pre_topc(C_313, D_311)!=g1_pre_topc(A_314, B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(k1_zfmisc_1(A_314))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.82  tff(c_2909, plain, (![B_322, A_323]: (u1_pre_topc('#skF_2')=B_322 | g1_pre_topc(A_323, B_322)!='#skF_3' | ~m1_subset_1(B_322, k1_zfmisc_1(k1_zfmisc_1(A_323))))), inference(superposition, [status(thm), theory('equality')], [c_2794, c_2839])).
% 4.79/1.82  tff(c_2921, plain, (![A_324]: (u1_pre_topc(A_324)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_324), u1_pre_topc(A_324))!='#skF_3' | ~l1_pre_topc(A_324))), inference(resolution, [status(thm)], [c_4, c_2909])).
% 4.79/1.82  tff(c_2932, plain, (![A_325]: (u1_pre_topc(A_325)=u1_pre_topc('#skF_2') | A_325!='#skF_3' | ~l1_pre_topc(A_325) | ~v1_pre_topc(A_325) | ~l1_pre_topc(A_325))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2921])).
% 4.79/1.82  tff(c_2935, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2722, c_2932])).
% 4.79/1.82  tff(c_2941, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2935])).
% 4.79/1.82  tff(c_2947, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_2794])).
% 4.79/1.82  tff(c_2698, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.79/1.82  tff(c_3086, plain, (![D_332, B_333, C_334, A_335]: (m1_pre_topc(D_332, B_333) | ~m1_pre_topc(C_334, A_335) | g1_pre_topc(u1_struct_0(D_332), u1_pre_topc(D_332))!=g1_pre_topc(u1_struct_0(C_334), u1_pre_topc(C_334)) | g1_pre_topc(u1_struct_0(B_333), u1_pre_topc(B_333))!=g1_pre_topc(u1_struct_0(A_335), u1_pre_topc(A_335)) | ~l1_pre_topc(D_332) | ~l1_pre_topc(C_334) | ~l1_pre_topc(B_333) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.79/1.82  tff(c_3088, plain, (![D_332, B_333]: (m1_pre_topc(D_332, B_333) | g1_pre_topc(u1_struct_0(D_332), u1_pre_topc(D_332))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(B_333), u1_pre_topc(B_333))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_332) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_333) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_2698, c_3086])).
% 4.79/1.82  tff(c_3198, plain, (![D_350, B_351]: (m1_pre_topc(D_350, B_351) | g1_pre_topc(u1_struct_0(D_350), u1_pre_topc(D_350))!='#skF_3' | g1_pre_topc(u1_struct_0(B_351), u1_pre_topc(B_351))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_350) | ~l1_pre_topc(B_351))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_2947, c_2941, c_2789, c_3088])).
% 4.79/1.82  tff(c_3200, plain, (![B_351]: (m1_pre_topc('#skF_3', B_351) | g1_pre_topc(u1_struct_0(B_351), u1_pre_topc(B_351))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(B_351))), inference(superposition, [status(thm), theory('equality')], [c_2947, c_3198])).
% 4.79/1.82  tff(c_3209, plain, (![B_351]: (m1_pre_topc('#skF_3', B_351) | g1_pre_topc(u1_struct_0(B_351), u1_pre_topc(B_351))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_351))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3200])).
% 4.79/1.82  tff(c_3216, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_3209])).
% 4.79/1.82  tff(c_3218, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3216])).
% 4.79/1.82  tff(c_3220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2699, c_3218])).
% 4.79/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.82  
% 4.79/1.82  Inference rules
% 4.79/1.82  ----------------------
% 4.79/1.82  #Ref     : 36
% 4.79/1.82  #Sup     : 634
% 4.79/1.82  #Fact    : 0
% 4.79/1.82  #Define  : 0
% 4.79/1.82  #Split   : 26
% 4.79/1.82  #Chain   : 0
% 4.79/1.82  #Close   : 0
% 4.79/1.82  
% 4.79/1.82  Ordering : KBO
% 4.79/1.82  
% 4.79/1.82  Simplification rules
% 4.79/1.82  ----------------------
% 4.79/1.82  #Subsume      : 186
% 4.79/1.82  #Demod        : 737
% 4.79/1.82  #Tautology    : 254
% 4.79/1.82  #SimpNegUnit  : 17
% 4.79/1.82  #BackRed      : 51
% 4.79/1.82  
% 4.79/1.82  #Partial instantiations: 0
% 4.79/1.82  #Strategies tried      : 1
% 4.79/1.82  
% 4.79/1.82  Timing (in seconds)
% 4.79/1.82  ----------------------
% 4.79/1.82  Preprocessing        : 0.30
% 4.79/1.82  Parsing              : 0.16
% 4.79/1.82  CNF conversion       : 0.02
% 4.79/1.82  Main loop            : 0.72
% 4.79/1.82  Inferencing          : 0.25
% 4.79/1.82  Reduction            : 0.25
% 4.79/1.82  Demodulation         : 0.16
% 4.79/1.82  BG Simplification    : 0.03
% 4.79/1.82  Subsumption          : 0.14
% 4.79/1.82  Abstraction          : 0.03
% 4.79/1.82  MUC search           : 0.00
% 4.79/1.82  Cooper               : 0.00
% 4.79/1.82  Total                : 1.09
% 4.79/1.82  Index Insertion      : 0.00
% 4.79/1.82  Index Deletion       : 0.00
% 4.79/1.82  Index Matching       : 0.00
% 4.79/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
