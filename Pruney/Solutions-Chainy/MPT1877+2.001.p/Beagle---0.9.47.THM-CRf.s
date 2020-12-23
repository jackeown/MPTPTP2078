%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:57 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 982 expanded)
%              Number of leaves         :   27 ( 343 expanded)
%              Depth                    :   17
%              Number of atoms          :  304 (3453 expanded)
%              Number of equality atoms :   34 ( 595 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v3_tex_2(C,A) )
                     => v3_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & C = D
                      & v2_tex_2(C,A) )
                   => v2_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).

tff(c_40,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    ~ v3_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_52,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_51,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_207,plain,(
    ! [A_78,B_79] :
      ( '#skF_1'(A_78,B_79) != B_79
      | v3_tex_2(B_79,A_78)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_217,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_207])).

tff(c_225,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_217])).

tff(c_226,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_225])).

tff(c_230,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    v3_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_119,plain,(
    ! [B_66,A_67] :
      ( v2_tex_2(B_66,A_67)
      | ~ v3_tex_2(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_132,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_119])).

tff(c_140,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_132])).

tff(c_20,plain,(
    ! [A_14] :
      ( m1_pre_topc(A_14,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141,plain,(
    ! [A_68,B_69] :
      ( m1_pre_topc(A_68,g1_pre_topc(u1_struct_0(B_69),u1_pre_topc(B_69)))
      | ~ m1_pre_topc(A_68,B_69)
      | ~ l1_pre_topc(B_69)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_102,plain,(
    ! [B_63,A_64] :
      ( m1_pre_topc(B_63,A_64)
      | ~ m1_pre_topc(B_63,g1_pre_topc(u1_struct_0(A_64),u1_pre_topc(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [B_63] :
      ( m1_pre_topc(B_63,'#skF_2')
      | ~ m1_pre_topc(B_63,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_111,plain,(
    ! [B_63] :
      ( m1_pre_topc(B_63,'#skF_2')
      | ~ m1_pre_topc(B_63,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_105])).

tff(c_145,plain,(
    ! [A_68] :
      ( m1_pre_topc(A_68,'#skF_2')
      | ~ m1_pre_topc(A_68,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_141,c_111])).

tff(c_154,plain,(
    ! [A_68] :
      ( m1_pre_topc(A_68,'#skF_2')
      | ~ m1_pre_topc(A_68,'#skF_3')
      | ~ l1_pre_topc(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_145])).

tff(c_151,plain,(
    ! [A_68] :
      ( m1_pre_topc(A_68,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_68,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_141])).

tff(c_182,plain,(
    ! [A_74] :
      ( m1_pre_topc(A_74,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_74,'#skF_2')
      | ~ l1_pre_topc(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_151])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( m1_pre_topc(B_7,A_5)
      | ~ m1_pre_topc(B_7,g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_188,plain,(
    ! [A_74] :
      ( m1_pre_topc(A_74,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_74,'#skF_2')
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_193,plain,(
    ! [A_75] :
      ( m1_pre_topc(A_75,'#skF_3')
      | ~ m1_pre_topc(A_75,'#skF_2')
      | ~ l1_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_188])).

tff(c_200,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_193])).

tff(c_204,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_200])).

tff(c_91,plain,(
    ! [B_59,A_60] :
      ( m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(u1_struct_0(B_59),u1_struct_0(A_60))
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_98,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(u1_struct_0(B_61),u1_struct_0(A_62))
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_250,plain,(
    ! [B_82,A_83] :
      ( u1_struct_0(B_82) = u1_struct_0(A_83)
      | ~ r1_tarski(u1_struct_0(A_83),u1_struct_0(B_82))
      | ~ m1_pre_topc(B_82,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_261,plain,(
    ! [B_84,A_85] :
      ( u1_struct_0(B_84) = u1_struct_0(A_85)
      | ~ m1_pre_topc(A_85,B_84)
      | ~ l1_pre_topc(B_84)
      | ~ m1_pre_topc(B_84,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_95,c_250])).

tff(c_263,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_204,c_261])).

tff(c_274,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_263])).

tff(c_282,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_285,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_282])).

tff(c_288,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_285])).

tff(c_291,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_288])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_291])).

tff(c_296,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_336,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_42])).

tff(c_732,plain,(
    ! [D_103,B_104,A_105] :
      ( v2_tex_2(D_103,B_104)
      | ~ v2_tex_2(D_103,A_105)
      | g1_pre_topc(u1_struct_0(B_104),u1_pre_topc(B_104)) != g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(B_104)))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(B_104)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_736,plain,(
    ! [D_103,B_104] :
      ( v2_tex_2(D_103,B_104)
      | ~ v2_tex_2(D_103,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_104),u1_pre_topc(B_104)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(B_104)))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc(B_104)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_732])).

tff(c_740,plain,(
    ! [D_103,B_104] :
      ( v2_tex_2(D_103,B_104)
      | ~ v2_tex_2(D_103,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_104),u1_pre_topc(B_104)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(B_104)))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_296,c_336,c_736])).

tff(c_2108,plain,(
    ! [D_103] :
      ( v2_tex_2(D_103,'#skF_3')
      | ~ v2_tex_2(D_103,'#skF_2')
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_740])).

tff(c_2116,plain,(
    ! [D_173] :
      ( v2_tex_2(D_173,'#skF_3')
      | ~ v2_tex_2(D_173,'#skF_2')
      | ~ m1_subset_1(D_173,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2108])).

tff(c_2144,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_2116])).

tff(c_2162,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2144])).

tff(c_2164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_2162])).

tff(c_2166,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_28,plain,(
    ! [A_15,B_21] :
      ( m1_subset_1('#skF_1'(A_15,B_21),k1_zfmisc_1(u1_struct_0(A_15)))
      | v3_tex_2(B_21,A_15)
      | ~ v2_tex_2(B_21,A_15)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2167,plain,(
    ! [B_174,A_175] :
      ( u1_struct_0(B_174) = u1_struct_0(A_175)
      | ~ r1_tarski(u1_struct_0(A_175),u1_struct_0(B_174))
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_2178,plain,(
    ! [B_176,A_177] :
      ( u1_struct_0(B_176) = u1_struct_0(A_177)
      | ~ m1_pre_topc(A_177,B_176)
      | ~ l1_pre_topc(B_176)
      | ~ m1_pre_topc(B_176,A_177)
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_95,c_2167])).

tff(c_2180,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_204,c_2178])).

tff(c_2191,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2180])).

tff(c_2218,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2191])).

tff(c_2221,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_2218])).

tff(c_2224,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2221])).

tff(c_2227,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2224])).

tff(c_2231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2227])).

tff(c_2232,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2191])).

tff(c_2165,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_2326,plain,(
    ! [B_180,A_181] :
      ( r1_tarski(B_180,'#skF_1'(A_181,B_180))
      | v3_tex_2(B_180,A_181)
      | ~ v2_tex_2(B_180,A_181)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2335,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_2326])).

tff(c_2342,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2166,c_2335])).

tff(c_2343,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2342])).

tff(c_2629,plain,(
    ! [C_191,B_192,A_193] :
      ( C_191 = B_192
      | ~ r1_tarski(B_192,C_191)
      | ~ v2_tex_2(C_191,A_193)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ v3_tex_2(B_192,A_193)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2635,plain,(
    ! [A_193] :
      ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
      | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_193)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ v3_tex_2('#skF_4',A_193)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_2343,c_2629])).

tff(c_2872,plain,(
    ! [A_207] :
      ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_207)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ v3_tex_2('#skF_4',A_207)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2165,c_2635])).

tff(c_2879,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2232,c_2872])).

tff(c_2888,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_51,c_2232,c_38,c_2879])).

tff(c_2890,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2888])).

tff(c_2893,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_2890])).

tff(c_2899,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_51,c_2166,c_2893])).

tff(c_2901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2899])).

tff(c_2902,plain,(
    ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2888])).

tff(c_2199,plain,(
    ! [A_178,B_179] :
      ( v2_tex_2('#skF_1'(A_178,B_179),A_178)
      | v3_tex_2(B_179,A_178)
      | ~ v2_tex_2(B_179,A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2206,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_2199])).

tff(c_2213,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2166,c_2206])).

tff(c_2214,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2213])).

tff(c_2903,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2888])).

tff(c_2253,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2232,c_42])).

tff(c_2705,plain,(
    ! [D_198,B_199,A_200] :
      ( v2_tex_2(D_198,B_199)
      | ~ v2_tex_2(D_198,A_200)
      | g1_pre_topc(u1_struct_0(B_199),u1_pre_topc(B_199)) != g1_pre_topc(u1_struct_0(A_200),u1_pre_topc(A_200))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0(B_199)))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(B_199)
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2707,plain,(
    ! [D_198,A_200] :
      ( v2_tex_2(D_198,'#skF_2')
      | ~ v2_tex_2(D_198,A_200)
      | g1_pre_topc(u1_struct_0(A_200),u1_pre_topc(A_200)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2232,c_2705])).

tff(c_2711,plain,(
    ! [D_198,A_200] :
      ( v2_tex_2(D_198,'#skF_2')
      | ~ v2_tex_2(D_198,A_200)
      | g1_pre_topc(u1_struct_0(A_200),u1_pre_topc(A_200)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2232,c_2253,c_2707])).

tff(c_4371,plain,(
    ! [D_198] :
      ( v2_tex_2(D_198,'#skF_2')
      | ~ v2_tex_2(D_198,'#skF_3')
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2711])).

tff(c_4379,plain,(
    ! [D_275] :
      ( v2_tex_2(D_275,'#skF_2')
      | ~ v2_tex_2(D_275,'#skF_3')
      | ~ m1_subset_1(D_275,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4371])).

tff(c_4385,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2903,c_4379])).

tff(c_4414,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2214,c_4385])).

tff(c_4416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2902,c_4414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.00  
% 5.54/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.00  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.54/2.00  
% 5.54/2.00  %Foreground sorts:
% 5.54/2.00  
% 5.54/2.00  
% 5.54/2.00  %Background operators:
% 5.54/2.00  
% 5.54/2.00  
% 5.54/2.00  %Foreground operators:
% 5.54/2.00  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.54/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.00  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.54/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.54/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.54/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.54/2.00  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.54/2.00  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.54/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.54/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.54/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.54/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.54/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.54/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.54/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.54/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.54/2.00  
% 5.54/2.02  tff(f_119, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v3_tex_2(C, A)) => v3_tex_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tex_2)).
% 5.54/2.02  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.54/2.02  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.54/2.02  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.54/2.02  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.54/2.02  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.54/2.02  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.54/2.02  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.54/2.02  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tex_2)).
% 5.54/2.02  tff(c_40, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_36, plain, (~v3_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_52, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 5.54/2.02  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_51, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 5.54/2.02  tff(c_207, plain, (![A_78, B_79]: ('#skF_1'(A_78, B_79)!=B_79 | v3_tex_2(B_79, A_78) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.54/2.02  tff(c_217, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_51, c_207])).
% 5.54/2.02  tff(c_225, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_217])).
% 5.54/2.02  tff(c_226, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_225])).
% 5.54/2.02  tff(c_230, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_226])).
% 5.54/2.02  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_38, plain, (v3_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_119, plain, (![B_66, A_67]: (v2_tex_2(B_66, A_67) | ~v3_tex_2(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.54/2.02  tff(c_132, plain, (v2_tex_2('#skF_4', '#skF_2') | ~v3_tex_2('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_119])).
% 5.54/2.02  tff(c_140, plain, (v2_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_132])).
% 5.54/2.02  tff(c_20, plain, (![A_14]: (m1_pre_topc(A_14, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.54/2.02  tff(c_141, plain, (![A_68, B_69]: (m1_pre_topc(A_68, g1_pre_topc(u1_struct_0(B_69), u1_pre_topc(B_69))) | ~m1_pre_topc(A_68, B_69) | ~l1_pre_topc(B_69) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.54/2.02  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.54/2.02  tff(c_102, plain, (![B_63, A_64]: (m1_pre_topc(B_63, A_64) | ~m1_pre_topc(B_63, g1_pre_topc(u1_struct_0(A_64), u1_pre_topc(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.54/2.02  tff(c_105, plain, (![B_63]: (m1_pre_topc(B_63, '#skF_2') | ~m1_pre_topc(B_63, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_102])).
% 5.54/2.02  tff(c_111, plain, (![B_63]: (m1_pre_topc(B_63, '#skF_2') | ~m1_pre_topc(B_63, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_105])).
% 5.54/2.02  tff(c_145, plain, (![A_68]: (m1_pre_topc(A_68, '#skF_2') | ~m1_pre_topc(A_68, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_141, c_111])).
% 5.54/2.02  tff(c_154, plain, (![A_68]: (m1_pre_topc(A_68, '#skF_2') | ~m1_pre_topc(A_68, '#skF_3') | ~l1_pre_topc(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_145])).
% 5.54/2.02  tff(c_151, plain, (![A_68]: (m1_pre_topc(A_68, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_68, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_68))), inference(superposition, [status(thm), theory('equality')], [c_42, c_141])).
% 5.54/2.02  tff(c_182, plain, (![A_74]: (m1_pre_topc(A_74, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_74, '#skF_2') | ~l1_pre_topc(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_151])).
% 5.54/2.02  tff(c_12, plain, (![B_7, A_5]: (m1_pre_topc(B_7, A_5) | ~m1_pre_topc(B_7, g1_pre_topc(u1_struct_0(A_5), u1_pre_topc(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.54/2.02  tff(c_188, plain, (![A_74]: (m1_pre_topc(A_74, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_74, '#skF_2') | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_182, c_12])).
% 5.54/2.02  tff(c_193, plain, (![A_75]: (m1_pre_topc(A_75, '#skF_3') | ~m1_pre_topc(A_75, '#skF_2') | ~l1_pre_topc(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_188])).
% 5.54/2.02  tff(c_200, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_193])).
% 5.54/2.02  tff(c_204, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_200])).
% 5.54/2.02  tff(c_91, plain, (![B_59, A_60]: (m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.54/2.02  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.54/2.02  tff(c_95, plain, (![B_59, A_60]: (r1_tarski(u1_struct_0(B_59), u1_struct_0(A_60)) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_91, c_8])).
% 5.54/2.02  tff(c_98, plain, (![B_61, A_62]: (r1_tarski(u1_struct_0(B_61), u1_struct_0(A_62)) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_91, c_8])).
% 5.54/2.02  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.02  tff(c_250, plain, (![B_82, A_83]: (u1_struct_0(B_82)=u1_struct_0(A_83) | ~r1_tarski(u1_struct_0(A_83), u1_struct_0(B_82)) | ~m1_pre_topc(B_82, A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_98, c_2])).
% 5.54/2.02  tff(c_261, plain, (![B_84, A_85]: (u1_struct_0(B_84)=u1_struct_0(A_85) | ~m1_pre_topc(A_85, B_84) | ~l1_pre_topc(B_84) | ~m1_pre_topc(B_84, A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_95, c_250])).
% 5.54/2.02  tff(c_263, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_204, c_261])).
% 5.54/2.02  tff(c_274, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_263])).
% 5.54/2.02  tff(c_282, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_274])).
% 5.54/2.02  tff(c_285, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_154, c_282])).
% 5.54/2.02  tff(c_288, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_285])).
% 5.54/2.02  tff(c_291, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_288])).
% 5.54/2.02  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_291])).
% 5.54/2.02  tff(c_296, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_274])).
% 5.54/2.02  tff(c_336, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_42])).
% 5.54/2.02  tff(c_732, plain, (![D_103, B_104, A_105]: (v2_tex_2(D_103, B_104) | ~v2_tex_2(D_103, A_105) | g1_pre_topc(u1_struct_0(B_104), u1_pre_topc(B_104))!=g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105)) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(B_104))) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(B_104) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.54/2.02  tff(c_736, plain, (![D_103, B_104]: (v2_tex_2(D_103, B_104) | ~v2_tex_2(D_103, '#skF_2') | g1_pre_topc(u1_struct_0(B_104), u1_pre_topc(B_104))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(B_104))) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(B_104) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_732])).
% 5.54/2.02  tff(c_740, plain, (![D_103, B_104]: (v2_tex_2(D_103, B_104) | ~v2_tex_2(D_103, '#skF_2') | g1_pre_topc(u1_struct_0(B_104), u1_pre_topc(B_104))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(B_104))) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_296, c_336, c_736])).
% 5.54/2.02  tff(c_2108, plain, (![D_103]: (v2_tex_2(D_103, '#skF_3') | ~v2_tex_2(D_103, '#skF_2') | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_740])).
% 5.54/2.02  tff(c_2116, plain, (![D_173]: (v2_tex_2(D_173, '#skF_3') | ~v2_tex_2(D_173, '#skF_2') | ~m1_subset_1(D_173, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2108])).
% 5.54/2.02  tff(c_2144, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_51, c_2116])).
% 5.54/2.02  tff(c_2162, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2144])).
% 5.54/2.02  tff(c_2164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_2162])).
% 5.54/2.02  tff(c_2166, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_226])).
% 5.54/2.02  tff(c_28, plain, (![A_15, B_21]: (m1_subset_1('#skF_1'(A_15, B_21), k1_zfmisc_1(u1_struct_0(A_15))) | v3_tex_2(B_21, A_15) | ~v2_tex_2(B_21, A_15) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.54/2.02  tff(c_2167, plain, (![B_174, A_175]: (u1_struct_0(B_174)=u1_struct_0(A_175) | ~r1_tarski(u1_struct_0(A_175), u1_struct_0(B_174)) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_98, c_2])).
% 5.54/2.02  tff(c_2178, plain, (![B_176, A_177]: (u1_struct_0(B_176)=u1_struct_0(A_177) | ~m1_pre_topc(A_177, B_176) | ~l1_pre_topc(B_176) | ~m1_pre_topc(B_176, A_177) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_95, c_2167])).
% 5.54/2.02  tff(c_2180, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_204, c_2178])).
% 5.54/2.02  tff(c_2191, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2180])).
% 5.54/2.02  tff(c_2218, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2191])).
% 5.54/2.02  tff(c_2221, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_154, c_2218])).
% 5.54/2.02  tff(c_2224, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2221])).
% 5.54/2.02  tff(c_2227, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_2224])).
% 5.54/2.02  tff(c_2231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_2227])).
% 5.54/2.02  tff(c_2232, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_2191])).
% 5.54/2.02  tff(c_2165, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_226])).
% 5.54/2.02  tff(c_2326, plain, (![B_180, A_181]: (r1_tarski(B_180, '#skF_1'(A_181, B_180)) | v3_tex_2(B_180, A_181) | ~v2_tex_2(B_180, A_181) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.54/2.02  tff(c_2335, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_51, c_2326])).
% 5.54/2.02  tff(c_2342, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2166, c_2335])).
% 5.54/2.02  tff(c_2343, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_2342])).
% 5.54/2.02  tff(c_2629, plain, (![C_191, B_192, A_193]: (C_191=B_192 | ~r1_tarski(B_192, C_191) | ~v2_tex_2(C_191, A_193) | ~m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(A_193))) | ~v3_tex_2(B_192, A_193) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.54/2.02  tff(c_2635, plain, (![A_193]: ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), A_193) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_193))) | ~v3_tex_2('#skF_4', A_193) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_2343, c_2629])).
% 5.54/2.02  tff(c_2872, plain, (![A_207]: (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), A_207) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_207))) | ~v3_tex_2('#skF_4', A_207) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(negUnitSimplification, [status(thm)], [c_2165, c_2635])).
% 5.54/2.02  tff(c_2879, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2232, c_2872])).
% 5.54/2.02  tff(c_2888, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_51, c_2232, c_38, c_2879])).
% 5.54/2.02  tff(c_2890, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2888])).
% 5.54/2.02  tff(c_2893, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_2890])).
% 5.54/2.02  tff(c_2899, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_51, c_2166, c_2893])).
% 5.54/2.02  tff(c_2901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2899])).
% 5.54/2.02  tff(c_2902, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_2888])).
% 5.54/2.02  tff(c_2199, plain, (![A_178, B_179]: (v2_tex_2('#skF_1'(A_178, B_179), A_178) | v3_tex_2(B_179, A_178) | ~v2_tex_2(B_179, A_178) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.54/2.02  tff(c_2206, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_51, c_2199])).
% 5.54/2.02  tff(c_2213, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2166, c_2206])).
% 5.54/2.02  tff(c_2214, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_2213])).
% 5.54/2.02  tff(c_2903, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2888])).
% 5.54/2.02  tff(c_2253, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2232, c_42])).
% 5.54/2.02  tff(c_2705, plain, (![D_198, B_199, A_200]: (v2_tex_2(D_198, B_199) | ~v2_tex_2(D_198, A_200) | g1_pre_topc(u1_struct_0(B_199), u1_pre_topc(B_199))!=g1_pre_topc(u1_struct_0(A_200), u1_pre_topc(A_200)) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0(B_199))) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(B_199) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.54/2.02  tff(c_2707, plain, (![D_198, A_200]: (v2_tex_2(D_198, '#skF_2') | ~v2_tex_2(D_198, A_200) | g1_pre_topc(u1_struct_0(A_200), u1_pre_topc(A_200))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_200))), inference(superposition, [status(thm), theory('equality')], [c_2232, c_2705])).
% 5.54/2.02  tff(c_2711, plain, (![D_198, A_200]: (v2_tex_2(D_198, '#skF_2') | ~v2_tex_2(D_198, A_200) | g1_pre_topc(u1_struct_0(A_200), u1_pre_topc(A_200))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2232, c_2253, c_2707])).
% 5.54/2.02  tff(c_4371, plain, (![D_198]: (v2_tex_2(D_198, '#skF_2') | ~v2_tex_2(D_198, '#skF_3') | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_2711])).
% 5.54/2.02  tff(c_4379, plain, (![D_275]: (v2_tex_2(D_275, '#skF_2') | ~v2_tex_2(D_275, '#skF_3') | ~m1_subset_1(D_275, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4371])).
% 5.54/2.02  tff(c_4385, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2903, c_4379])).
% 5.54/2.02  tff(c_4414, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2214, c_4385])).
% 5.54/2.02  tff(c_4416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2902, c_4414])).
% 5.54/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.02  
% 5.54/2.02  Inference rules
% 5.54/2.02  ----------------------
% 5.54/2.02  #Ref     : 5
% 5.54/2.02  #Sup     : 794
% 5.54/2.02  #Fact    : 0
% 5.54/2.02  #Define  : 0
% 5.54/2.02  #Split   : 20
% 5.54/2.02  #Chain   : 0
% 5.54/2.02  #Close   : 0
% 5.54/2.02  
% 5.54/2.02  Ordering : KBO
% 5.54/2.02  
% 5.54/2.02  Simplification rules
% 5.54/2.02  ----------------------
% 5.54/2.02  #Subsume      : 335
% 5.54/2.02  #Demod        : 1106
% 5.54/2.02  #Tautology    : 155
% 5.54/2.02  #SimpNegUnit  : 151
% 5.54/2.02  #BackRed      : 8
% 5.54/2.02  
% 5.54/2.02  #Partial instantiations: 0
% 5.54/2.02  #Strategies tried      : 1
% 5.54/2.02  
% 5.54/2.02  Timing (in seconds)
% 5.54/2.02  ----------------------
% 5.54/2.03  Preprocessing        : 0.32
% 5.54/2.03  Parsing              : 0.16
% 5.54/2.03  CNF conversion       : 0.02
% 5.54/2.03  Main loop            : 0.95
% 5.54/2.03  Inferencing          : 0.33
% 5.54/2.03  Reduction            : 0.32
% 5.54/2.03  Demodulation         : 0.22
% 5.54/2.03  BG Simplification    : 0.03
% 5.54/2.03  Subsumption          : 0.21
% 5.54/2.03  Abstraction          : 0.04
% 5.54/2.03  MUC search           : 0.00
% 5.54/2.03  Cooper               : 0.00
% 5.54/2.03  Total                : 1.30
% 5.54/2.03  Index Insertion      : 0.00
% 5.54/2.03  Index Deletion       : 0.00
% 5.54/2.03  Index Matching       : 0.00
% 5.54/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
