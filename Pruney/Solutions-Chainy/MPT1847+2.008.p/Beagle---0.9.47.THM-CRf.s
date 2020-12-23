%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:53 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  126 (1546 expanded)
%              Number of leaves         :   30 ( 552 expanded)
%              Depth                    :   21
%              Number of atoms          :  254 (4720 expanded)
%              Number of equality atoms :   26 ( 664 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_40,axiom,(
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

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : ~ v1_subset_1(k2_subset_1(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_51,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_70,plain,(
    ! [B_42,A_43] :
      ( l1_pre_topc(B_42)
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_86,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_79])).

tff(c_26,plain,(
    ! [A_19] :
      ( m1_pre_topc(A_19,A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_143,plain,(
    ! [B_59,A_60] :
      ( u1_struct_0(B_59) = '#skF_1'(A_60,B_59)
      | v1_tex_2(B_59,A_60)
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_146,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_143,c_40])).

tff(c_149,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_146])).

tff(c_44,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_151,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_44])).

tff(c_253,plain,(
    ! [A_68,B_69] :
      ( m1_pre_topc(A_68,g1_pre_topc(u1_struct_0(B_69),u1_pre_topc(B_69)))
      | ~ m1_pre_topc(A_68,B_69)
      | ~ l1_pre_topc(B_69)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_262,plain,(
    ! [A_68] :
      ( m1_pre_topc(A_68,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_68,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_253])).

tff(c_298,plain,(
    ! [A_71] :
      ( m1_pre_topc(A_71,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_71,'#skF_3')
      | ~ l1_pre_topc(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_262])).

tff(c_76,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_70])).

tff(c_83,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_76])).

tff(c_18,plain,(
    ! [B_12,A_10] :
      ( m1_pre_topc(B_12,A_10)
      | ~ m1_pre_topc(B_12,g1_pre_topc(u1_struct_0(A_10),u1_pre_topc(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_161,plain,(
    ! [B_12] :
      ( m1_pre_topc(B_12,'#skF_4')
      | ~ m1_pre_topc(B_12,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_18])).

tff(c_173,plain,(
    ! [B_12] :
      ( m1_pre_topc(B_12,'#skF_4')
      | ~ m1_pre_topc(B_12,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_161])).

tff(c_313,plain,(
    ! [A_72] :
      ( m1_pre_topc(A_72,'#skF_4')
      | ~ m1_pre_topc(A_72,'#skF_3')
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_298,c_173])).

tff(c_317,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_313])).

tff(c_320,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_317])).

tff(c_265,plain,(
    ! [A_68] :
      ( m1_pre_topc(A_68,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_68,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_253])).

tff(c_332,plain,(
    ! [A_74] :
      ( m1_pre_topc(A_74,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_74,'#skF_4')
      | ~ l1_pre_topc(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_265])).

tff(c_122,plain,(
    ! [B_54,A_55] :
      ( m1_pre_topc(B_54,A_55)
      | ~ m1_pre_topc(B_54,g1_pre_topc(u1_struct_0(A_55),u1_pre_topc(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_125,plain,(
    ! [B_54] :
      ( m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_122])).

tff(c_131,plain,(
    ! [B_54] :
      ( m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_125])).

tff(c_150,plain,(
    ! [B_54] :
      ( m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_131])).

tff(c_343,plain,(
    ! [A_74] :
      ( m1_pre_topc(A_74,'#skF_3')
      | ~ m1_pre_topc(A_74,'#skF_4')
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_332,c_150])).

tff(c_32,plain,(
    ! [B_26,A_20] :
      ( u1_struct_0(B_26) = '#skF_1'(A_20,B_26)
      | v1_tex_2(B_26,A_20)
      | ~ m1_pre_topc(B_26,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    ! [B_18,A_16] :
      ( m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_454,plain,(
    ! [B_88,A_89] :
      ( v1_subset_1(u1_struct_0(B_88),u1_struct_0(A_89))
      | ~ m1_subset_1(u1_struct_0(B_88),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ v1_tex_2(B_88,A_89)
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_472,plain,(
    ! [B_90,A_91] :
      ( v1_subset_1(u1_struct_0(B_90),u1_struct_0(A_91))
      | ~ v1_tex_2(B_90,A_91)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_24,c_454])).

tff(c_486,plain,(
    ! [A_92] :
      ( ~ v1_tex_2(A_92,A_92)
      | ~ m1_pre_topc(A_92,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_472,c_51])).

tff(c_793,plain,(
    ! [A_97] :
      ( u1_struct_0(A_97) = '#skF_1'(A_97,A_97)
      | ~ m1_pre_topc(A_97,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_32,c_486])).

tff(c_797,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_343,c_793])).

tff(c_810,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_320,c_797])).

tff(c_167,plain,(
    ! [B_18] :
      ( m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | ~ m1_pre_topc(B_18,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_24])).

tff(c_195,plain,(
    ! [B_64] :
      ( m1_subset_1(u1_struct_0(B_64),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | ~ m1_pre_topc(B_64,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_167])).

tff(c_204,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_195])).

tff(c_237,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_240,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_237])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_240])).

tff(c_246,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_492,plain,(
    ! [A_93] :
      ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_93))
      | ~ v1_tex_2('#skF_4',A_93)
      | ~ m1_pre_topc('#skF_4',A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_472])).

tff(c_499,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4'))
    | ~ v1_tex_2('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_492])).

tff(c_505,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4'))
    | ~ v1_tex_2('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_246,c_499])).

tff(c_506,plain,(
    ~ v1_tex_2('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_505])).

tff(c_509,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_506])).

tff(c_512,plain,(
    '#skF_1'('#skF_2','#skF_4') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_246,c_149,c_509])).

tff(c_113,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_121,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(u1_struct_0(B_52),u1_struct_0(A_53))
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_113,c_12])).

tff(c_158,plain,(
    ! [B_52] :
      ( r1_tarski(u1_struct_0(B_52),'#skF_1'('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_52,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_121])).

tff(c_171,plain,(
    ! [B_52] :
      ( r1_tarski(u1_struct_0(B_52),'#skF_1'('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_52,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_158])).

tff(c_529,plain,(
    ! [B_52] :
      ( r1_tarski(u1_struct_0(B_52),'#skF_1'('#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_52,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_171])).

tff(c_823,plain,
    ( r1_tarski('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_529])).

tff(c_877,plain,(
    r1_tarski('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_823])).

tff(c_530,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_149])).

tff(c_862,plain,(
    ! [B_52] :
      ( r1_tarski(u1_struct_0(B_52),'#skF_1'('#skF_3','#skF_3'))
      | ~ m1_pre_topc(B_52,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_121])).

tff(c_941,plain,(
    ! [B_99] :
      ( r1_tarski(u1_struct_0(B_99),'#skF_1'('#skF_3','#skF_3'))
      | ~ m1_pre_topc(B_99,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_862])).

tff(c_952,plain,
    ( r1_tarski('#skF_1'('#skF_4','#skF_4'),'#skF_1'('#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_941])).

tff(c_1037,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_1044,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_343,c_1037])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_246,c_1044])).

tff(c_1049,plain,(
    r1_tarski('#skF_1'('#skF_4','#skF_4'),'#skF_1'('#skF_3','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1064,plain,
    ( '#skF_1'('#skF_3','#skF_3') = '#skF_1'('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1049,c_2])).

tff(c_1067,plain,(
    '#skF_1'('#skF_3','#skF_3') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_1064])).

tff(c_1073,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_810])).

tff(c_345,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75,B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | v1_tex_2(B_76,A_75)
      | ~ m1_pre_topc(B_76,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_356,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_1'(A_75,B_76),u1_struct_0(A_75))
      | v1_tex_2(B_76,A_75)
      | ~ m1_pre_topc(B_76,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_345,c_12])).

tff(c_534,plain,
    ( r1_tarski('#skF_1'('#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_356])).

tff(c_544,plain,
    ( r1_tarski('#skF_1'('#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_534])).

tff(c_545,plain,(
    r1_tarski('#skF_1'('#skF_4','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_544])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [B_48,A_49] :
      ( v1_subset_1(B_48,A_49)
      | B_48 = A_49
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_103,plain,(
    ! [A_5,B_6] :
      ( v1_subset_1(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_30,plain,(
    ! [A_20,B_26] :
      ( ~ v1_subset_1('#skF_1'(A_20,B_26),u1_struct_0(A_20))
      | v1_tex_2(B_26,A_20)
      | ~ m1_pre_topc(B_26,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_540,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_30])).

tff(c_550,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_540])).

tff(c_551,plain,(
    ~ v1_subset_1('#skF_1'('#skF_4','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_550])).

tff(c_629,plain,
    ( u1_struct_0('#skF_2') = '#skF_1'('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_1'('#skF_4','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_103,c_551])).

tff(c_632,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_629])).

tff(c_470,plain,(
    ! [B_18,A_16] :
      ( v1_subset_1(u1_struct_0(B_18),u1_struct_0(A_16))
      | ~ v1_tex_2(B_18,A_16)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_454])).

tff(c_667,plain,(
    ! [B_18] :
      ( v1_subset_1(u1_struct_0(B_18),'#skF_1'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_18,'#skF_2')
      | ~ m1_pre_topc(B_18,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_470])).

tff(c_1611,plain,(
    ! [B_120] :
      ( v1_subset_1(u1_struct_0(B_120),'#skF_1'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_120,'#skF_2')
      | ~ m1_pre_topc(B_120,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_667])).

tff(c_1614,plain,
    ( v1_subset_1('#skF_1'('#skF_4','#skF_4'),'#skF_1'('#skF_4','#skF_4'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_1611])).

tff(c_1622,plain,(
    v1_subset_1('#skF_1'('#skF_4','#skF_4'),'#skF_1'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_1614])).

tff(c_1624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.63  
% 3.57/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.64  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.57/1.64  
% 3.57/1.64  %Foreground sorts:
% 3.57/1.64  
% 3.57/1.64  
% 3.57/1.64  %Background operators:
% 3.57/1.64  
% 3.57/1.64  
% 3.57/1.64  %Foreground operators:
% 3.57/1.64  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.57/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.64  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.57/1.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.57/1.64  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.57/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.57/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.57/1.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.57/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.64  
% 3.87/1.66  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.87/1.66  tff(f_36, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.87/1.66  tff(f_110, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 3.87/1.66  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.87/1.66  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.87/1.66  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.87/1.66  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.87/1.66  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.87/1.66  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.87/1.66  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.87/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.87/1.66  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.87/1.66  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.66  tff(c_10, plain, (![A_4]: (~v1_subset_1(k2_subset_1(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.87/1.66  tff(c_51, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.87/1.66  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.87/1.66  tff(c_42, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.87/1.66  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.87/1.66  tff(c_70, plain, (![B_42, A_43]: (l1_pre_topc(B_42) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.87/1.66  tff(c_79, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_70])).
% 3.87/1.66  tff(c_86, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_79])).
% 3.87/1.66  tff(c_26, plain, (![A_19]: (m1_pre_topc(A_19, A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.87/1.66  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.87/1.66  tff(c_143, plain, (![B_59, A_60]: (u1_struct_0(B_59)='#skF_1'(A_60, B_59) | v1_tex_2(B_59, A_60) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.66  tff(c_40, plain, (~v1_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.87/1.66  tff(c_146, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_143, c_40])).
% 3.87/1.66  tff(c_149, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_146])).
% 3.87/1.66  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.87/1.66  tff(c_151, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_44])).
% 3.87/1.66  tff(c_253, plain, (![A_68, B_69]: (m1_pre_topc(A_68, g1_pre_topc(u1_struct_0(B_69), u1_pre_topc(B_69))) | ~m1_pre_topc(A_68, B_69) | ~l1_pre_topc(B_69) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.87/1.66  tff(c_262, plain, (![A_68]: (m1_pre_topc(A_68, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_68, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_68))), inference(superposition, [status(thm), theory('equality')], [c_151, c_253])).
% 3.87/1.66  tff(c_298, plain, (![A_71]: (m1_pre_topc(A_71, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_71, '#skF_3') | ~l1_pre_topc(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_262])).
% 3.87/1.66  tff(c_76, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_70])).
% 3.87/1.66  tff(c_83, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_76])).
% 3.87/1.66  tff(c_18, plain, (![B_12, A_10]: (m1_pre_topc(B_12, A_10) | ~m1_pre_topc(B_12, g1_pre_topc(u1_struct_0(A_10), u1_pre_topc(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.87/1.66  tff(c_161, plain, (![B_12]: (m1_pre_topc(B_12, '#skF_4') | ~m1_pre_topc(B_12, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_18])).
% 3.87/1.66  tff(c_173, plain, (![B_12]: (m1_pre_topc(B_12, '#skF_4') | ~m1_pre_topc(B_12, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_161])).
% 3.87/1.66  tff(c_313, plain, (![A_72]: (m1_pre_topc(A_72, '#skF_4') | ~m1_pre_topc(A_72, '#skF_3') | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_298, c_173])).
% 3.87/1.66  tff(c_317, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_313])).
% 3.87/1.66  tff(c_320, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_317])).
% 3.87/1.66  tff(c_265, plain, (![A_68]: (m1_pre_topc(A_68, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_68, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_68))), inference(superposition, [status(thm), theory('equality')], [c_149, c_253])).
% 3.87/1.66  tff(c_332, plain, (![A_74]: (m1_pre_topc(A_74, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_74, '#skF_4') | ~l1_pre_topc(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_265])).
% 3.87/1.66  tff(c_122, plain, (![B_54, A_55]: (m1_pre_topc(B_54, A_55) | ~m1_pre_topc(B_54, g1_pre_topc(u1_struct_0(A_55), u1_pre_topc(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.87/1.66  tff(c_125, plain, (![B_54]: (m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_122])).
% 3.87/1.66  tff(c_131, plain, (![B_54]: (m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_125])).
% 3.87/1.66  tff(c_150, plain, (![B_54]: (m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_131])).
% 3.87/1.66  tff(c_343, plain, (![A_74]: (m1_pre_topc(A_74, '#skF_3') | ~m1_pre_topc(A_74, '#skF_4') | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_332, c_150])).
% 3.87/1.66  tff(c_32, plain, (![B_26, A_20]: (u1_struct_0(B_26)='#skF_1'(A_20, B_26) | v1_tex_2(B_26, A_20) | ~m1_pre_topc(B_26, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.66  tff(c_24, plain, (![B_18, A_16]: (m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.87/1.66  tff(c_454, plain, (![B_88, A_89]: (v1_subset_1(u1_struct_0(B_88), u1_struct_0(A_89)) | ~m1_subset_1(u1_struct_0(B_88), k1_zfmisc_1(u1_struct_0(A_89))) | ~v1_tex_2(B_88, A_89) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.66  tff(c_472, plain, (![B_90, A_91]: (v1_subset_1(u1_struct_0(B_90), u1_struct_0(A_91)) | ~v1_tex_2(B_90, A_91) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_24, c_454])).
% 3.87/1.66  tff(c_486, plain, (![A_92]: (~v1_tex_2(A_92, A_92) | ~m1_pre_topc(A_92, A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_472, c_51])).
% 3.87/1.66  tff(c_793, plain, (![A_97]: (u1_struct_0(A_97)='#skF_1'(A_97, A_97) | ~m1_pre_topc(A_97, A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_32, c_486])).
% 3.87/1.66  tff(c_797, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_343, c_793])).
% 3.87/1.66  tff(c_810, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_320, c_797])).
% 3.87/1.66  tff(c_167, plain, (![B_18]: (m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~m1_pre_topc(B_18, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_24])).
% 3.87/1.66  tff(c_195, plain, (![B_64]: (m1_subset_1(u1_struct_0(B_64), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~m1_pre_topc(B_64, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_167])).
% 3.87/1.66  tff(c_204, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_149, c_195])).
% 3.87/1.66  tff(c_237, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_204])).
% 3.87/1.66  tff(c_240, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_237])).
% 3.87/1.66  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_240])).
% 3.87/1.66  tff(c_246, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_204])).
% 3.87/1.66  tff(c_492, plain, (![A_93]: (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_93)) | ~v1_tex_2('#skF_4', A_93) | ~m1_pre_topc('#skF_4', A_93) | ~l1_pre_topc(A_93))), inference(superposition, [status(thm), theory('equality')], [c_149, c_472])).
% 3.87/1.66  tff(c_499, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_149, c_492])).
% 3.87/1.66  tff(c_505, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_246, c_499])).
% 3.87/1.66  tff(c_506, plain, (~v1_tex_2('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_51, c_505])).
% 3.87/1.66  tff(c_509, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_506])).
% 3.87/1.66  tff(c_512, plain, ('#skF_1'('#skF_2', '#skF_4')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_246, c_149, c_509])).
% 3.87/1.66  tff(c_113, plain, (![B_52, A_53]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.87/1.66  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.87/1.66  tff(c_121, plain, (![B_52, A_53]: (r1_tarski(u1_struct_0(B_52), u1_struct_0(A_53)) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_113, c_12])).
% 3.87/1.66  tff(c_158, plain, (![B_52]: (r1_tarski(u1_struct_0(B_52), '#skF_1'('#skF_2', '#skF_4')) | ~m1_pre_topc(B_52, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_121])).
% 3.87/1.66  tff(c_171, plain, (![B_52]: (r1_tarski(u1_struct_0(B_52), '#skF_1'('#skF_2', '#skF_4')) | ~m1_pre_topc(B_52, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_158])).
% 3.87/1.66  tff(c_529, plain, (![B_52]: (r1_tarski(u1_struct_0(B_52), '#skF_1'('#skF_4', '#skF_4')) | ~m1_pre_topc(B_52, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_171])).
% 3.87/1.66  tff(c_823, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_810, c_529])).
% 3.87/1.66  tff(c_877, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_823])).
% 3.87/1.66  tff(c_530, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_149])).
% 3.87/1.66  tff(c_862, plain, (![B_52]: (r1_tarski(u1_struct_0(B_52), '#skF_1'('#skF_3', '#skF_3')) | ~m1_pre_topc(B_52, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_810, c_121])).
% 3.87/1.66  tff(c_941, plain, (![B_99]: (r1_tarski(u1_struct_0(B_99), '#skF_1'('#skF_3', '#skF_3')) | ~m1_pre_topc(B_99, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_862])).
% 3.87/1.66  tff(c_952, plain, (r1_tarski('#skF_1'('#skF_4', '#skF_4'), '#skF_1'('#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_530, c_941])).
% 3.87/1.66  tff(c_1037, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_952])).
% 3.87/1.66  tff(c_1044, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_343, c_1037])).
% 3.87/1.66  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_246, c_1044])).
% 3.87/1.66  tff(c_1049, plain, (r1_tarski('#skF_1'('#skF_4', '#skF_4'), '#skF_1'('#skF_3', '#skF_3'))), inference(splitRight, [status(thm)], [c_952])).
% 3.87/1.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.66  tff(c_1064, plain, ('#skF_1'('#skF_3', '#skF_3')='#skF_1'('#skF_4', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1049, c_2])).
% 3.87/1.66  tff(c_1067, plain, ('#skF_1'('#skF_3', '#skF_3')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_877, c_1064])).
% 3.87/1.66  tff(c_1073, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_810])).
% 3.87/1.66  tff(c_345, plain, (![A_75, B_76]: (m1_subset_1('#skF_1'(A_75, B_76), k1_zfmisc_1(u1_struct_0(A_75))) | v1_tex_2(B_76, A_75) | ~m1_pre_topc(B_76, A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.66  tff(c_356, plain, (![A_75, B_76]: (r1_tarski('#skF_1'(A_75, B_76), u1_struct_0(A_75)) | v1_tex_2(B_76, A_75) | ~m1_pre_topc(B_76, A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_345, c_12])).
% 3.87/1.66  tff(c_534, plain, (r1_tarski('#skF_1'('#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_512, c_356])).
% 3.87/1.66  tff(c_544, plain, (r1_tarski('#skF_1'('#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_534])).
% 3.87/1.66  tff(c_545, plain, (r1_tarski('#skF_1'('#skF_4', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_544])).
% 3.87/1.66  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.87/1.66  tff(c_99, plain, (![B_48, A_49]: (v1_subset_1(B_48, A_49) | B_48=A_49 | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.87/1.66  tff(c_103, plain, (![A_5, B_6]: (v1_subset_1(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_14, c_99])).
% 3.87/1.66  tff(c_30, plain, (![A_20, B_26]: (~v1_subset_1('#skF_1'(A_20, B_26), u1_struct_0(A_20)) | v1_tex_2(B_26, A_20) | ~m1_pre_topc(B_26, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.87/1.66  tff(c_540, plain, (~v1_subset_1('#skF_1'('#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_512, c_30])).
% 3.87/1.66  tff(c_550, plain, (~v1_subset_1('#skF_1'('#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_540])).
% 3.87/1.66  tff(c_551, plain, (~v1_subset_1('#skF_1'('#skF_4', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_550])).
% 3.87/1.66  tff(c_629, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_4', '#skF_4') | ~r1_tarski('#skF_1'('#skF_4', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_103, c_551])).
% 3.87/1.66  tff(c_632, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_545, c_629])).
% 3.87/1.66  tff(c_470, plain, (![B_18, A_16]: (v1_subset_1(u1_struct_0(B_18), u1_struct_0(A_16)) | ~v1_tex_2(B_18, A_16) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_24, c_454])).
% 3.87/1.66  tff(c_667, plain, (![B_18]: (v1_subset_1(u1_struct_0(B_18), '#skF_1'('#skF_4', '#skF_4')) | ~v1_tex_2(B_18, '#skF_2') | ~m1_pre_topc(B_18, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_632, c_470])).
% 3.87/1.66  tff(c_1611, plain, (![B_120]: (v1_subset_1(u1_struct_0(B_120), '#skF_1'('#skF_4', '#skF_4')) | ~v1_tex_2(B_120, '#skF_2') | ~m1_pre_topc(B_120, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_667])).
% 3.87/1.66  tff(c_1614, plain, (v1_subset_1('#skF_1'('#skF_4', '#skF_4'), '#skF_1'('#skF_4', '#skF_4')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1073, c_1611])).
% 3.87/1.66  tff(c_1622, plain, (v1_subset_1('#skF_1'('#skF_4', '#skF_4'), '#skF_1'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_1614])).
% 3.87/1.66  tff(c_1624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_1622])).
% 3.87/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.66  
% 3.87/1.66  Inference rules
% 3.87/1.66  ----------------------
% 3.87/1.66  #Ref     : 0
% 3.87/1.66  #Sup     : 321
% 3.87/1.66  #Fact    : 0
% 3.87/1.66  #Define  : 0
% 3.87/1.66  #Split   : 6
% 3.87/1.66  #Chain   : 0
% 3.87/1.66  #Close   : 0
% 3.87/1.66  
% 3.87/1.66  Ordering : KBO
% 3.87/1.66  
% 3.87/1.66  Simplification rules
% 3.87/1.66  ----------------------
% 3.87/1.66  #Subsume      : 49
% 3.87/1.66  #Demod        : 395
% 3.87/1.66  #Tautology    : 126
% 3.87/1.66  #SimpNegUnit  : 29
% 3.87/1.66  #BackRed      : 29
% 3.87/1.66  
% 3.87/1.66  #Partial instantiations: 0
% 3.87/1.66  #Strategies tried      : 1
% 3.87/1.66  
% 3.87/1.66  Timing (in seconds)
% 3.87/1.66  ----------------------
% 3.87/1.66  Preprocessing        : 0.34
% 3.87/1.66  Parsing              : 0.18
% 3.87/1.66  CNF conversion       : 0.02
% 3.87/1.66  Main loop            : 0.54
% 3.87/1.66  Inferencing          : 0.19
% 3.87/1.66  Reduction            : 0.19
% 3.87/1.66  Demodulation         : 0.13
% 3.87/1.66  BG Simplification    : 0.03
% 3.87/1.66  Subsumption          : 0.11
% 3.87/1.66  Abstraction          : 0.02
% 3.87/1.66  MUC search           : 0.00
% 3.87/1.66  Cooper               : 0.00
% 3.87/1.66  Total                : 0.93
% 3.87/1.66  Index Insertion      : 0.00
% 3.87/1.66  Index Deletion       : 0.00
% 3.87/1.66  Index Matching       : 0.00
% 3.87/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
