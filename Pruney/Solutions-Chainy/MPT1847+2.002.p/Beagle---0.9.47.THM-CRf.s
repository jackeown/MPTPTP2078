%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:52 EST 2020

% Result     : Theorem 9.96s
% Output     : CNFRefutation 10.17s
% Verified   : 
% Statistics : Number of formulae       :  341 (5020 expanded)
%              Number of leaves         :   42 (1712 expanded)
%              Depth                    :   21
%              Number of atoms          :  752 (14872 expanded)
%              Number of equality atoms :   81 (1897 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_162,axiom,(
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

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_52,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_86,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_169,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_zfmisc_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_62,plain,(
    v1_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_90,plain,(
    ! [B_67,A_68] :
      ( l1_pre_topc(B_67)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_90])).

tff(c_106,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_99])).

tff(c_44,plain,(
    ! [A_39] :
      ( m1_pre_topc(A_39,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    ! [B_49,A_43] :
      ( u1_struct_0(B_49) = '#skF_2'(A_43,B_49)
      | v1_tex_2(B_49,A_43)
      | ~ m1_pre_topc(B_49,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_42,plain,(
    ! [B_38,A_36] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14755,plain,(
    ! [B_645,A_646] :
      ( v1_subset_1(u1_struct_0(B_645),u1_struct_0(A_646))
      | ~ m1_subset_1(u1_struct_0(B_645),k1_zfmisc_1(u1_struct_0(A_646)))
      | ~ v1_tex_2(B_645,A_646)
      | ~ m1_pre_topc(B_645,A_646)
      | ~ l1_pre_topc(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_16555,plain,(
    ! [B_697,A_698] :
      ( v1_subset_1(u1_struct_0(B_697),u1_struct_0(A_698))
      | ~ v1_tex_2(B_697,A_698)
      | ~ m1_pre_topc(B_697,A_698)
      | ~ l1_pre_topc(A_698) ) ),
    inference(resolution,[status(thm)],[c_42,c_14755])).

tff(c_14,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_20] : ~ v1_subset_1(k2_subset_1(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_71,plain,(
    ! [A_20] : ~ v1_subset_1(A_20,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_16622,plain,(
    ! [A_699] :
      ( ~ v1_tex_2(A_699,A_699)
      | ~ m1_pre_topc(A_699,A_699)
      | ~ l1_pre_topc(A_699) ) ),
    inference(resolution,[status(thm)],[c_16555,c_71])).

tff(c_16628,plain,(
    ! [A_700] :
      ( u1_struct_0(A_700) = '#skF_2'(A_700,A_700)
      | ~ m1_pre_topc(A_700,A_700)
      | ~ l1_pre_topc(A_700) ) ),
    inference(resolution,[status(thm)],[c_52,c_16622])).

tff(c_16664,plain,(
    ! [A_701] :
      ( u1_struct_0(A_701) = '#skF_2'(A_701,A_701)
      | ~ l1_pre_topc(A_701) ) ),
    inference(resolution,[status(thm)],[c_44,c_16628])).

tff(c_16686,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_16664])).

tff(c_66,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_307,plain,(
    ! [B_113,A_114] :
      ( u1_struct_0(B_113) = '#skF_2'(A_114,B_113)
      | v1_tex_2(B_113,A_114)
      | ~ m1_pre_topc(B_113,A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    ~ v1_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_310,plain,
    ( u1_struct_0('#skF_5') = '#skF_2'('#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_307,c_60])).

tff(c_313,plain,(
    u1_struct_0('#skF_5') = '#skF_2'('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_310])).

tff(c_64,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_314,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_64])).

tff(c_12377,plain,(
    ! [A_565,B_566] :
      ( m1_pre_topc(A_565,g1_pre_topc(u1_struct_0(B_566),u1_pre_topc(B_566)))
      | ~ m1_pre_topc(A_565,B_566)
      | ~ l1_pre_topc(B_566)
      | ~ l1_pre_topc(A_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12392,plain,(
    ! [A_565] :
      ( m1_pre_topc(A_565,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_565,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_12377])).

tff(c_13081,plain,(
    ! [A_598] :
      ( m1_pre_topc(A_598,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_598,'#skF_4')
      | ~ l1_pre_topc(A_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_12392])).

tff(c_96,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_90])).

tff(c_103,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_96])).

tff(c_241,plain,(
    ! [B_105,A_106] :
      ( m1_pre_topc(B_105,A_106)
      | ~ m1_pre_topc(B_105,g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_244,plain,(
    ! [B_105] :
      ( m1_pre_topc(B_105,'#skF_5')
      | ~ m1_pre_topc(B_105,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_241])).

tff(c_250,plain,(
    ! [B_105] :
      ( m1_pre_topc(B_105,'#skF_5')
      | ~ m1_pre_topc(B_105,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_244])).

tff(c_354,plain,(
    ! [B_105] :
      ( m1_pre_topc(B_105,'#skF_5')
      | ~ m1_pre_topc(B_105,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_250])).

tff(c_13462,plain,(
    ! [A_604] :
      ( m1_pre_topc(A_604,'#skF_5')
      | ~ m1_pre_topc(A_604,'#skF_4')
      | ~ l1_pre_topc(A_604) ) ),
    inference(resolution,[status(thm)],[c_13081,c_354])).

tff(c_12978,plain,(
    ! [B_592,A_593] :
      ( v1_subset_1(u1_struct_0(B_592),u1_struct_0(A_593))
      | ~ m1_subset_1(u1_struct_0(B_592),k1_zfmisc_1(u1_struct_0(A_593)))
      | ~ v1_tex_2(B_592,A_593)
      | ~ m1_pre_topc(B_592,A_593)
      | ~ l1_pre_topc(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_13011,plain,(
    ! [B_594,A_595] :
      ( v1_subset_1(u1_struct_0(B_594),u1_struct_0(A_595))
      | ~ v1_tex_2(B_594,A_595)
      | ~ m1_pre_topc(B_594,A_595)
      | ~ l1_pre_topc(A_595) ) ),
    inference(resolution,[status(thm)],[c_42,c_12978])).

tff(c_13046,plain,(
    ! [A_596] :
      ( ~ v1_tex_2(A_596,A_596)
      | ~ m1_pre_topc(A_596,A_596)
      | ~ l1_pre_topc(A_596) ) ),
    inference(resolution,[status(thm)],[c_13011,c_71])).

tff(c_13052,plain,(
    ! [A_597] :
      ( u1_struct_0(A_597) = '#skF_2'(A_597,A_597)
      | ~ m1_pre_topc(A_597,A_597)
      | ~ l1_pre_topc(A_597) ) ),
    inference(resolution,[status(thm)],[c_52,c_13046])).

tff(c_13136,plain,(
    ! [A_599] :
      ( u1_struct_0(A_599) = '#skF_2'(A_599,A_599)
      | ~ l1_pre_topc(A_599) ) ),
    inference(resolution,[status(thm)],[c_44,c_13052])).

tff(c_13153,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_13136])).

tff(c_334,plain,(
    ! [B_38] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
      | ~ m1_pre_topc(B_38,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_42])).

tff(c_7771,plain,(
    ! [B_392] :
      ( m1_subset_1(u1_struct_0(B_392),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
      | ~ m1_pre_topc(B_392,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_334])).

tff(c_7789,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_7771])).

tff(c_7940,plain,(
    ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7789])).

tff(c_7943,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_7940])).

tff(c_7947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_7943])).

tff(c_7949,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_7789])).

tff(c_8388,plain,(
    ! [B_427,A_428] :
      ( v1_subset_1(u1_struct_0(B_427),u1_struct_0(A_428))
      | ~ m1_subset_1(u1_struct_0(B_427),k1_zfmisc_1(u1_struct_0(A_428)))
      | ~ v1_tex_2(B_427,A_428)
      | ~ m1_pre_topc(B_427,A_428)
      | ~ l1_pre_topc(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8459,plain,(
    ! [B_431,A_432] :
      ( v1_subset_1(u1_struct_0(B_431),u1_struct_0(A_432))
      | ~ v1_tex_2(B_431,A_432)
      | ~ m1_pre_topc(B_431,A_432)
      | ~ l1_pre_topc(A_432) ) ),
    inference(resolution,[status(thm)],[c_42,c_8388])).

tff(c_8526,plain,(
    ! [A_434] :
      ( ~ v1_tex_2(A_434,A_434)
      | ~ m1_pre_topc(A_434,A_434)
      | ~ l1_pre_topc(A_434) ) ),
    inference(resolution,[status(thm)],[c_8459,c_71])).

tff(c_8532,plain,(
    ! [A_435] :
      ( u1_struct_0(A_435) = '#skF_2'(A_435,A_435)
      | ~ m1_pre_topc(A_435,A_435)
      | ~ l1_pre_topc(A_435) ) ),
    inference(resolution,[status(thm)],[c_52,c_8526])).

tff(c_8581,plain,(
    ! [A_436] :
      ( u1_struct_0(A_436) = '#skF_2'(A_436,A_436)
      | ~ l1_pre_topc(A_436) ) ),
    inference(resolution,[status(thm)],[c_44,c_8532])).

tff(c_8594,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_8581])).

tff(c_8621,plain,(
    g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_314])).

tff(c_8006,plain,(
    ! [A_398,B_399] :
      ( m1_pre_topc(A_398,g1_pre_topc(u1_struct_0(B_399),u1_pre_topc(B_399)))
      | ~ m1_pre_topc(A_398,B_399)
      | ~ l1_pre_topc(B_399)
      | ~ l1_pre_topc(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8024,plain,(
    ! [A_398] :
      ( m1_pre_topc(A_398,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_398,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_8006])).

tff(c_8033,plain,(
    ! [A_398] :
      ( m1_pre_topc(A_398,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_398,'#skF_5')
      | ~ l1_pre_topc(A_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_8024])).

tff(c_12116,plain,(
    ! [A_553] :
      ( m1_pre_topc(A_553,g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_553,'#skF_5')
      | ~ l1_pre_topc(A_553) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8621,c_8033])).

tff(c_259,plain,(
    ! [B_108,A_109] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_108),u1_pre_topc(B_108)),A_109)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    ! [B_26,A_24] :
      ( l1_pre_topc(B_26)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_283,plain,(
    ! [B_110,A_111] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_110),u1_pre_topc(B_110)))
      | ~ m1_pre_topc(B_110,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_259,c_30])).

tff(c_293,plain,(
    ! [A_39] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_44,c_283])).

tff(c_318,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_293])).

tff(c_341,plain,(
    l1_pre_topc(g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_318])).

tff(c_8866,plain,(
    l1_pre_topc(g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8621,c_341])).

tff(c_8597,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_8581])).

tff(c_8404,plain,(
    ! [B_38,A_36] :
      ( v1_subset_1(u1_struct_0(B_38),u1_struct_0(A_36))
      | ~ v1_tex_2(B_38,A_36)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_42,c_8388])).

tff(c_8755,plain,(
    ! [B_38] :
      ( v1_subset_1(u1_struct_0(B_38),'#skF_2'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_38,'#skF_3')
      | ~ m1_pre_topc(B_38,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8597,c_8404])).

tff(c_9933,plain,(
    ! [B_477] :
      ( v1_subset_1(u1_struct_0(B_477),'#skF_2'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_477,'#skF_3')
      | ~ m1_pre_topc(B_477,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8755])).

tff(c_9941,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3'))
    | ~ v1_tex_2('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8594,c_9933])).

tff(c_9950,plain,(
    v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_9941])).

tff(c_175,plain,(
    ! [B_95,A_96] :
      ( m1_subset_1(u1_struct_0(B_95),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_193,plain,(
    ! [B_95,A_96] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ v1_xboole_0(u1_struct_0(A_96))
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_175,c_22])).

tff(c_328,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_5'))
      | ~ m1_pre_topc(B_95,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_193])).

tff(c_347,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_5'))
      | ~ m1_pre_topc(B_95,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_328])).

tff(c_7797,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_8688,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_95,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8594,c_193])).

tff(c_8733,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
      | ~ m1_pre_topc(B_95,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_8688])).

tff(c_9617,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8733])).

tff(c_1154,plain,(
    ! [B_162,A_163] :
      ( v1_subset_1(u1_struct_0(B_162),u1_struct_0(A_163))
      | ~ m1_subset_1(u1_struct_0(B_162),k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ v1_tex_2(B_162,A_163)
      | ~ m1_pre_topc(B_162,A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1199,plain,(
    ! [B_166,A_167] :
      ( v1_subset_1(u1_struct_0(B_166),u1_struct_0(A_167))
      | ~ v1_tex_2(B_166,A_167)
      | ~ m1_pre_topc(B_166,A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_42,c_1154])).

tff(c_1233,plain,(
    ! [A_170] :
      ( ~ v1_tex_2(A_170,A_170)
      | ~ m1_pre_topc(A_170,A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_1199,c_71])).

tff(c_1239,plain,(
    ! [A_171] :
      ( u1_struct_0(A_171) = '#skF_2'(A_171,A_171)
      | ~ m1_pre_topc(A_171,A_171)
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_52,c_1233])).

tff(c_1320,plain,(
    ! [A_172] :
      ( u1_struct_0(A_172) = '#skF_2'(A_172,A_172)
      | ~ l1_pre_topc(A_172) ) ),
    inference(resolution,[status(thm)],[c_44,c_1239])).

tff(c_1333,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_1320])).

tff(c_1336,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1320])).

tff(c_1555,plain,(
    ! [B_38] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ m1_pre_topc(B_38,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_42])).

tff(c_1743,plain,(
    ! [B_180] :
      ( m1_subset_1(u1_struct_0(B_180),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ m1_pre_topc(B_180,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1555])).

tff(c_1772,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_1743])).

tff(c_1786,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1772])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1('#skF_1'(A_11,B_12),A_11)
      | B_12 = A_11
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1026,plain,(
    ! [A_151,B_152] :
      ( m1_subset_1('#skF_2'(A_151,B_152),k1_zfmisc_1(u1_struct_0(A_151)))
      | v1_tex_2(B_152,A_151)
      | ~ m1_pre_topc(B_152,A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    ! [B_54,A_53] :
      ( v1_subset_1(B_54,A_53)
      | B_54 = A_53
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2713,plain,(
    ! [A_212,B_213] :
      ( v1_subset_1('#skF_2'(A_212,B_213),u1_struct_0(A_212))
      | u1_struct_0(A_212) = '#skF_2'(A_212,B_213)
      | v1_tex_2(B_213,A_212)
      | ~ m1_pre_topc(B_213,A_212)
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_1026,c_56])).

tff(c_50,plain,(
    ! [A_43,B_49] :
      ( ~ v1_subset_1('#skF_2'(A_43,B_49),u1_struct_0(A_43))
      | v1_tex_2(B_49,A_43)
      | ~ m1_pre_topc(B_49,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4482,plain,(
    ! [A_241,B_242] :
      ( u1_struct_0(A_241) = '#skF_2'(A_241,B_242)
      | v1_tex_2(B_242,A_241)
      | ~ m1_pre_topc(B_242,A_241)
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_2713,c_50])).

tff(c_4498,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4482,c_60])).

tff(c_4511,plain,(
    '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1336,c_4498])).

tff(c_385,plain,(
    ! [B_115] :
      ( m1_subset_1(u1_struct_0(B_115),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
      | ~ m1_pre_topc(B_115,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_334])).

tff(c_403,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_385])).

tff(c_537,plain,(
    ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_568,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_537])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_568])).

tff(c_574,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_825,plain,(
    ! [A_143,B_144] :
      ( m1_pre_topc(A_143,g1_pre_topc(u1_struct_0(B_144),u1_pre_topc(B_144)))
      | ~ m1_pre_topc(A_143,B_144)
      | ~ l1_pre_topc(B_144)
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_843,plain,(
    ! [A_143] :
      ( m1_pre_topc(A_143,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_143,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_825])).

tff(c_905,plain,(
    ! [A_147] :
      ( m1_pre_topc(A_147,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_147,'#skF_5')
      | ~ l1_pre_topc(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_843])).

tff(c_32,plain,(
    ! [B_29,A_27] :
      ( m1_pre_topc(B_29,A_27)
      | ~ m1_pre_topc(B_29,g1_pre_topc(u1_struct_0(A_27),u1_pre_topc(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_367,plain,(
    ! [B_29] :
      ( m1_pre_topc(B_29,'#skF_4')
      | ~ m1_pre_topc(B_29,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_32])).

tff(c_376,plain,(
    ! [B_29] :
      ( m1_pre_topc(B_29,'#skF_4')
      | ~ m1_pre_topc(B_29,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_367])).

tff(c_935,plain,(
    ! [A_148] :
      ( m1_pre_topc(A_148,'#skF_4')
      | ~ m1_pre_topc(A_148,'#skF_5')
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_905,c_376])).

tff(c_945,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_574,c_935])).

tff(c_967,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_945])).

tff(c_4,plain,(
    ! [A_3] :
      ( v1_zfmisc_1(A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [B_23,A_21] :
      ( v1_zfmisc_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_21))
      | ~ v1_zfmisc_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_194,plain,(
    ! [B_95,A_96] :
      ( v1_zfmisc_1(u1_struct_0(B_95))
      | ~ v1_zfmisc_1(u1_struct_0(A_96))
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_175,c_28])).

tff(c_326,plain,(
    ! [B_95] :
      ( v1_zfmisc_1(u1_struct_0(B_95))
      | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_5'))
      | ~ m1_pre_topc(B_95,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_194])).

tff(c_345,plain,(
    ! [B_95] :
      ( v1_zfmisc_1(u1_struct_0(B_95))
      | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_5'))
      | ~ m1_pre_topc(B_95,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_326])).

tff(c_380,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_384,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_380])).

tff(c_732,plain,(
    ! [A_134] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_pre_topc('#skF_5',A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_42])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_145,plain,(
    ! [B_5,A_84,A_4] :
      ( r2_hidden(B_5,A_84)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_734,plain,(
    ! [B_5,A_134] :
      ( r2_hidden(B_5,u1_struct_0(A_134))
      | ~ m1_subset_1(B_5,'#skF_2'('#skF_3','#skF_5'))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_732,c_145])).

tff(c_761,plain,(
    ! [B_5,A_134] :
      ( r2_hidden(B_5,u1_struct_0(A_134))
      | ~ m1_subset_1(B_5,'#skF_2'('#skF_3','#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_384,c_734])).

tff(c_1359,plain,(
    ! [B_5] :
      ( r2_hidden(B_5,'#skF_2'('#skF_4','#skF_4'))
      | ~ m1_subset_1(B_5,'#skF_2'('#skF_3','#skF_5'))
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_761])).

tff(c_2052,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,'#skF_2'('#skF_4','#skF_4'))
      | ~ m1_subset_1(B_185,'#skF_2'('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_967,c_1359])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_1'(A_11,B_12),B_12)
      | B_12 = A_11
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2062,plain,(
    ! [A_11] :
      ( A_11 = '#skF_2'('#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1(A_11))
      | ~ m1_subset_1('#skF_1'(A_11,'#skF_2'('#skF_4','#skF_4')),'#skF_2'('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2052,c_18])).

tff(c_7639,plain,(
    ! [A_386] :
      ( A_386 = '#skF_2'('#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1(A_386))
      | ~ m1_subset_1('#skF_1'(A_386,'#skF_2'('#skF_4','#skF_4')),'#skF_2'('#skF_3','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4511,c_2062])).

tff(c_7646,plain,
    ( '#skF_2'('#skF_3','#skF_3') = '#skF_2'('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_20,c_7639])).

tff(c_7653,plain,(
    '#skF_2'('#skF_3','#skF_3') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_7646])).

tff(c_4418,plain,(
    ! [A_239,B_240] :
      ( u1_struct_0(A_239) = '#skF_2'(A_239,B_240)
      | v1_tex_2(B_240,A_239)
      | ~ m1_pre_topc(B_240,A_239)
      | ~ l1_pre_topc(A_239) ) ),
    inference(resolution,[status(thm)],[c_2713,c_50])).

tff(c_1170,plain,(
    ! [B_38,A_36] :
      ( v1_subset_1(u1_struct_0(B_38),u1_struct_0(A_36))
      | ~ v1_tex_2(B_38,A_36)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_42,c_1154])).

tff(c_1356,plain,(
    ! [B_38] :
      ( v1_subset_1(u1_struct_0(B_38),'#skF_2'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_38,'#skF_4')
      | ~ m1_pre_topc(B_38,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_1170])).

tff(c_3641,plain,(
    ! [B_234] :
      ( v1_subset_1(u1_struct_0(B_234),'#skF_2'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_234,'#skF_4')
      | ~ m1_pre_topc(B_234,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1356])).

tff(c_3652,plain,
    ( v1_subset_1('#skF_2'('#skF_3','#skF_5'),'#skF_2'('#skF_4','#skF_4'))
    | ~ v1_tex_2('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_3641])).

tff(c_3658,plain,
    ( v1_subset_1('#skF_2'('#skF_3','#skF_5'),'#skF_2'('#skF_4','#skF_4'))
    | ~ v1_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_3652])).

tff(c_3665,plain,(
    ~ v1_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3658])).

tff(c_4421,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4418,c_3665])).

tff(c_4440,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_967,c_1333,c_4421])).

tff(c_3668,plain,
    ( u1_struct_0('#skF_5') = '#skF_2'('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_3665])).

tff(c_3671,plain,(
    '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_967,c_313,c_3668])).

tff(c_1487,plain,(
    ! [B_38] :
      ( v1_subset_1(u1_struct_0(B_38),'#skF_2'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_38,'#skF_3')
      | ~ m1_pre_topc(B_38,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_1170])).

tff(c_2904,plain,(
    ! [B_220] :
      ( v1_subset_1(u1_struct_0(B_220),'#skF_2'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_220,'#skF_3')
      | ~ m1_pre_topc(B_220,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1487])).

tff(c_2912,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3'))
    | ~ v1_tex_2('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_2904])).

tff(c_2921,plain,(
    v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_2912])).

tff(c_3375,plain,(
    ! [A_224,B_225] :
      ( u1_struct_0(A_224) = '#skF_2'(A_224,B_225)
      | v1_tex_2(B_225,A_224)
      | ~ m1_pre_topc(B_225,A_224)
      | ~ l1_pre_topc(A_224) ) ),
    inference(resolution,[status(thm)],[c_2713,c_50])).

tff(c_3394,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_3375,c_60])).

tff(c_3410,plain,(
    '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1336,c_3394])).

tff(c_840,plain,(
    ! [A_143] :
      ( m1_pre_topc(A_143,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_143,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_825])).

tff(c_853,plain,(
    ! [A_145] :
      ( m1_pre_topc(A_145,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_145,'#skF_4')
      | ~ l1_pre_topc(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_840])).

tff(c_870,plain,(
    ! [A_145] :
      ( m1_pre_topc(A_145,'#skF_5')
      | ~ m1_pre_topc(A_145,'#skF_4')
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_853,c_354])).

tff(c_349,plain,(
    ! [B_38] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
      | ~ m1_pre_topc(B_38,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_334])).

tff(c_1405,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_349])).

tff(c_2425,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1405])).

tff(c_2428,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_870,c_2425])).

tff(c_2431,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2428])).

tff(c_2434,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2431])).

tff(c_2438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2434])).

tff(c_2440,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1405])).

tff(c_1214,plain,(
    ! [B_166] :
      ( v1_subset_1(u1_struct_0(B_166),'#skF_2'('#skF_3','#skF_5'))
      | ~ v1_tex_2(B_166,'#skF_5')
      | ~ m1_pre_topc(B_166,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_1199])).

tff(c_2695,plain,(
    ! [B_211] :
      ( v1_subset_1(u1_struct_0(B_211),'#skF_2'('#skF_3','#skF_5'))
      | ~ v1_tex_2(B_211,'#skF_5')
      | ~ m1_pre_topc(B_211,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1214])).

tff(c_2703,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | ~ v1_tex_2('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_2695])).

tff(c_2709,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | ~ v1_tex_2('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2440,c_2703])).

tff(c_2748,plain,(
    ~ v1_tex_2('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2709])).

tff(c_2751,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2748])).

tff(c_2754,plain,(
    '#skF_2'('#skF_5','#skF_4') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2440,c_1333,c_2751])).

tff(c_711,plain,(
    ! [A_131,B_132] :
      ( ~ v1_subset_1('#skF_2'(A_131,B_132),u1_struct_0(A_131))
      | v1_tex_2(B_132,A_131)
      | ~ m1_pre_topc(B_132,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_714,plain,(
    ! [B_132] :
      ( ~ v1_subset_1('#skF_2'('#skF_5',B_132),'#skF_2'('#skF_3','#skF_5'))
      | v1_tex_2(B_132,'#skF_5')
      | ~ m1_pre_topc(B_132,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_711])).

tff(c_716,plain,(
    ! [B_132] :
      ( ~ v1_subset_1('#skF_2'('#skF_5',B_132),'#skF_2'('#skF_3','#skF_5'))
      | v1_tex_2(B_132,'#skF_5')
      | ~ m1_pre_topc(B_132,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_714])).

tff(c_2767,plain,
    ( ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | v1_tex_2('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2754,c_716])).

tff(c_2783,plain,
    ( ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | v1_tex_2('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2440,c_2767])).

tff(c_2784,plain,(
    ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2748,c_2783])).

tff(c_3413,plain,(
    ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3410,c_2784])).

tff(c_3441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2921,c_3413])).

tff(c_3442,plain,(
    v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2709])).

tff(c_3672,plain,(
    v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3671,c_3442])).

tff(c_4464,plain,(
    v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4440,c_3672])).

tff(c_4475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_4464])).

tff(c_4477,plain,(
    v1_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3658])).

tff(c_4538,plain,(
    u1_struct_0('#skF_5') = '#skF_2'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4511,c_313])).

tff(c_1431,plain,(
    ! [B_38] :
      ( v1_subset_1(u1_struct_0(B_38),'#skF_2'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_38,'#skF_4')
      | ~ m1_pre_topc(B_38,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1356])).

tff(c_4562,plain,
    ( v1_subset_1('#skF_2'('#skF_3','#skF_3'),'#skF_2'('#skF_4','#skF_4'))
    | ~ v1_tex_2('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4538,c_1431])).

tff(c_4681,plain,(
    v1_subset_1('#skF_2'('#skF_3','#skF_3'),'#skF_2'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_4477,c_4562])).

tff(c_7714,plain,(
    v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7653,c_4681])).

tff(c_7739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_7714])).

tff(c_7741,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_8021,plain,(
    ! [A_398] :
      ( m1_pre_topc(A_398,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_398,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_8006])).

tff(c_8307,plain,(
    ! [A_424] :
      ( m1_pre_topc(A_424,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_pre_topc(A_424,'#skF_4')
      | ~ l1_pre_topc(A_424) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_8021])).

tff(c_8333,plain,(
    ! [A_424] :
      ( m1_pre_topc(A_424,'#skF_5')
      | ~ m1_pre_topc(A_424,'#skF_4')
      | ~ l1_pre_topc(A_424) ) ),
    inference(resolution,[status(thm)],[c_8307,c_354])).

tff(c_7740,plain,(
    ! [B_95] :
      ( v1_zfmisc_1(u1_struct_0(B_95))
      | ~ m1_pre_topc(B_95,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_8675,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8594,c_7740])).

tff(c_8888,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8675])).

tff(c_8946,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8333,c_8888])).

tff(c_8949,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_8946])).

tff(c_8952,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_8949])).

tff(c_8956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_8952])).

tff(c_8958,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_8675])).

tff(c_8672,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5')))
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8594,c_349])).

tff(c_9805,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8958,c_8672])).

tff(c_46,plain,(
    ! [B_42,A_40] :
      ( v1_xboole_0(B_42)
      | ~ v1_subset_1(B_42,A_40)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_40))
      | ~ v1_zfmisc_1(A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_9813,plain,
    ( v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
    | ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_5'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_9805,c_46])).

tff(c_9835,plain,
    ( v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
    | ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7741,c_9813])).

tff(c_9836,plain,(
    ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_7797,c_9617,c_9835])).

tff(c_8474,plain,(
    ! [B_431] :
      ( v1_subset_1(u1_struct_0(B_431),'#skF_2'('#skF_3','#skF_5'))
      | ~ v1_tex_2(B_431,'#skF_5')
      | ~ m1_pre_topc(B_431,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_8459])).

tff(c_10121,plain,(
    ! [B_481] :
      ( v1_subset_1(u1_struct_0(B_481),'#skF_2'('#skF_3','#skF_5'))
      | ~ v1_tex_2(B_481,'#skF_5')
      | ~ m1_pre_topc(B_481,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_8474])).

tff(c_10132,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | ~ v1_tex_2('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8594,c_10121])).

tff(c_10139,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | ~ v1_tex_2('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8958,c_10132])).

tff(c_10140,plain,(
    ~ v1_tex_2('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_9836,c_10139])).

tff(c_10146,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_10140])).

tff(c_10149,plain,(
    '#skF_2'('#skF_5','#skF_4') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_8958,c_8594,c_10146])).

tff(c_8255,plain,(
    ! [A_419,B_420] :
      ( m1_subset_1('#skF_2'(A_419,B_420),k1_zfmisc_1(u1_struct_0(A_419)))
      | v1_tex_2(B_420,A_419)
      | ~ m1_pre_topc(B_420,A_419)
      | ~ l1_pre_topc(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_10360,plain,(
    ! [A_495,B_496] :
      ( v1_subset_1('#skF_2'(A_495,B_496),u1_struct_0(A_495))
      | u1_struct_0(A_495) = '#skF_2'(A_495,B_496)
      | v1_tex_2(B_496,A_495)
      | ~ m1_pre_topc(B_496,A_495)
      | ~ l1_pre_topc(A_495) ) ),
    inference(resolution,[status(thm)],[c_8255,c_56])).

tff(c_10368,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_2'('#skF_5','#skF_4')
    | v1_tex_2('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10149,c_10360])).

tff(c_10384,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_5'))
    | '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_4','#skF_4')
    | v1_tex_2('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_8958,c_10149,c_313,c_313,c_10368])).

tff(c_10385,plain,(
    '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_10140,c_9836,c_10384])).

tff(c_10429,plain,
    ( ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | v1_tex_2('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10385,c_50])).

tff(c_10439,plain,(
    v1_tex_2('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_9950,c_8597,c_10429])).

tff(c_10441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10439])).

tff(c_10443,plain,(
    v1_xboole_0('#skF_2'('#skF_4','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8733])).

tff(c_7863,plain,(
    ! [B_396] :
      ( m1_pre_topc(B_396,'#skF_4')
      | ~ m1_pre_topc(B_396,g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_367])).

tff(c_7875,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_44,c_7863])).

tff(c_7884,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2'('#skF_3','#skF_5'),u1_pre_topc('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_7875])).

tff(c_8860,plain,(
    m1_pre_topc(g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8621,c_7884])).

tff(c_10442,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ m1_pre_topc(B_95,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_8733])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10477,plain,(
    ! [A_498] :
      ( A_498 = '#skF_2'('#skF_4','#skF_4')
      | ~ v1_xboole_0(A_498) ) ),
    inference(resolution,[status(thm)],[c_10443,c_2])).

tff(c_10523,plain,(
    ! [B_502] :
      ( u1_struct_0(B_502) = '#skF_2'('#skF_4','#skF_4')
      | ~ m1_pre_topc(B_502,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10442,c_10477])).

tff(c_10549,plain,(
    u1_struct_0(g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_2'('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_8860,c_10523])).

tff(c_8158,plain,(
    ! [A_411] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ m1_pre_topc('#skF_5',A_411)
      | ~ l1_pre_topc(A_411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_42])).

tff(c_8172,plain,(
    ! [A_411] :
      ( v1_xboole_0('#skF_2'('#skF_3','#skF_5'))
      | ~ v1_xboole_0(u1_struct_0(A_411))
      | ~ m1_pre_topc('#skF_5',A_411)
      | ~ l1_pre_topc(A_411) ) ),
    inference(resolution,[status(thm)],[c_8158,c_22])).

tff(c_8192,plain,(
    ! [A_411] :
      ( ~ v1_xboole_0(u1_struct_0(A_411))
      | ~ m1_pre_topc('#skF_5',A_411)
      | ~ l1_pre_topc(A_411) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7797,c_8172])).

tff(c_10747,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_5',g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10549,c_8192])).

tff(c_10826,plain,(
    ~ m1_pre_topc('#skF_5',g1_pre_topc('#skF_2'('#skF_4','#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8866,c_10443,c_10747])).

tff(c_12143,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12116,c_10826])).

tff(c_12185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_7949,c_12143])).

tff(c_12186,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ m1_pre_topc(B_95,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_13193,plain,
    ( v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13153,c_12186])).

tff(c_13415,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_13193])).

tff(c_13465,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_13462,c_13415])).

tff(c_13489,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_13465])).

tff(c_13573,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_13489])).

tff(c_13577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_13573])).

tff(c_13578,plain,(
    v1_xboole_0('#skF_2'('#skF_4','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13193])).

tff(c_13156,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_13136])).

tff(c_13579,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_13193])).

tff(c_12187,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_12227,plain,(
    ! [A_557] :
      ( A_557 = '#skF_2'('#skF_3','#skF_5')
      | ~ v1_xboole_0(A_557) ) ),
    inference(resolution,[status(thm)],[c_12187,c_2])).

tff(c_12234,plain,(
    ! [B_95] :
      ( u1_struct_0(B_95) = '#skF_2'('#skF_3','#skF_5')
      | ~ m1_pre_topc(B_95,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12186,c_12227])).

tff(c_13588,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_13579,c_12234])).

tff(c_13607,plain,(
    '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13153,c_13588])).

tff(c_13663,plain,
    ( ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | v1_tex_2('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13607,c_50])).

tff(c_13670,plain,
    ( ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3'))
    | v1_tex_2('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_13156,c_13663])).

tff(c_13671,plain,(
    ~ v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13670])).

tff(c_54,plain,(
    ! [A_43,B_49] :
      ( m1_subset_1('#skF_2'(A_43,B_49),k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_tex_2(B_49,A_43)
      | ~ m1_pre_topc(B_49,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_13660,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_tex_2('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13607,c_54])).

tff(c_13667,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
    | v1_tex_2('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_13156,c_13660])).

tff(c_13668,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13667])).

tff(c_13833,plain,
    ( v1_subset_1('#skF_2'('#skF_4','#skF_4'),'#skF_2'('#skF_3','#skF_3'))
    | '#skF_2'('#skF_3','#skF_3') = '#skF_2'('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_13668,c_56])).

tff(c_13854,plain,(
    '#skF_2'('#skF_3','#skF_3') = '#skF_2'('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_13671,c_13833])).

tff(c_222,plain,(
    ! [B_101,A_102] :
      ( v1_zfmisc_1(u1_struct_0(B_101))
      | ~ v1_zfmisc_1(u1_struct_0(A_102))
      | ~ m1_pre_topc(B_101,A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_175,c_28])).

tff(c_227,plain,(
    ! [B_103,A_104] :
      ( v1_zfmisc_1(u1_struct_0(B_103))
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v1_xboole_0(u1_struct_0(A_104)) ) ),
    inference(resolution,[status(thm)],[c_4,c_222])).

tff(c_231,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_227])).

tff(c_237,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_231])).

tff(c_252,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_13251,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13156,c_252])).

tff(c_13866,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13854,c_13251])).

tff(c_13870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13578,c_13866])).

tff(c_13872,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_13879,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ m1_pre_topc(B_95,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_13872,c_193])).

tff(c_13884,plain,(
    ! [B_95] :
      ( v1_xboole_0(u1_struct_0(B_95))
      | ~ m1_pre_topc(B_95,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_13879])).

tff(c_16879,plain,
    ( v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16686,c_13884])).

tff(c_16934,plain,(
    v1_xboole_0('#skF_2'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16879])).

tff(c_13926,plain,(
    ! [B_616] :
      ( v1_xboole_0(u1_struct_0(B_616))
      | ~ m1_pre_topc(B_616,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_13879])).

tff(c_13885,plain,(
    ! [A_1] :
      ( u1_struct_0('#skF_3') = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_13872,c_2])).

tff(c_13953,plain,(
    ! [B_618] :
      ( u1_struct_0(B_618) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_618,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_13926,c_13885])).

tff(c_13983,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_13953])).

tff(c_13982,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_13953])).

tff(c_14036,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13983,c_13982])).

tff(c_14204,plain,(
    ! [B_624,A_625] :
      ( u1_struct_0(B_624) = '#skF_2'(A_625,B_624)
      | v1_tex_2(B_624,A_625)
      | ~ m1_pre_topc(B_624,A_625)
      | ~ l1_pre_topc(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_14207,plain,
    ( u1_struct_0('#skF_5') = '#skF_2'('#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14204,c_60])).

tff(c_14210,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_14036,c_14207])).

tff(c_16813,plain,(
    '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16686,c_14210])).

tff(c_16689,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_16664])).

tff(c_14215,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14210,c_13983])).

tff(c_16690,plain,(
    '#skF_2'('#skF_3','#skF_5') = '#skF_2'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16689,c_14215])).

tff(c_17201,plain,(
    '#skF_2'('#skF_3','#skF_3') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16813,c_16690])).

tff(c_17260,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17201,c_16689])).

tff(c_24,plain,(
    ! [B_19,A_17] :
      ( ~ v1_subset_1(B_19,A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_192,plain,(
    ! [B_95,A_96] :
      ( ~ v1_subset_1(u1_struct_0(B_95),u1_struct_0(A_96))
      | ~ v1_xboole_0(u1_struct_0(A_96))
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_175,c_24])).

tff(c_19125,plain,(
    ! [A_745,B_746] :
      ( ~ v1_xboole_0(u1_struct_0(A_745))
      | ~ v1_tex_2(B_746,A_745)
      | ~ m1_pre_topc(B_746,A_745)
      | ~ l1_pre_topc(A_745) ) ),
    inference(resolution,[status(thm)],[c_16555,c_192])).

tff(c_19133,plain,(
    ! [B_746] :
      ( ~ v1_xboole_0('#skF_2'('#skF_4','#skF_4'))
      | ~ v1_tex_2(B_746,'#skF_3')
      | ~ m1_pre_topc(B_746,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17260,c_19125])).

tff(c_19167,plain,(
    ! [B_748] :
      ( ~ v1_tex_2(B_748,'#skF_3')
      | ~ m1_pre_topc(B_748,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_16934,c_19133])).

tff(c_19174,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_19167])).

tff(c_19181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_19174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.96/3.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.17/3.81  
% 10.17/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.17/3.81  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 10.17/3.81  
% 10.17/3.81  %Foreground sorts:
% 10.17/3.81  
% 10.17/3.81  
% 10.17/3.81  %Background operators:
% 10.17/3.81  
% 10.17/3.81  
% 10.17/3.81  %Foreground operators:
% 10.17/3.81  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.17/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.17/3.81  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 10.17/3.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.17/3.81  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 10.17/3.81  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 10.17/3.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.17/3.81  tff('#skF_5', type, '#skF_5': $i).
% 10.17/3.81  tff('#skF_3', type, '#skF_3': $i).
% 10.17/3.81  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.17/3.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.17/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.17/3.81  tff('#skF_4', type, '#skF_4': $i).
% 10.17/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.17/3.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.17/3.81  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 10.17/3.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.17/3.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.17/3.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.17/3.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.17/3.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.17/3.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.17/3.81  
% 10.17/3.85  tff(f_184, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 10.17/3.85  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.17/3.85  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 10.17/3.85  tff(f_162, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 10.17/3.85  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 10.17/3.85  tff(f_52, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.17/3.85  tff(f_86, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 10.17/3.85  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 10.17/3.85  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 10.17/3.85  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 10.17/3.85  tff(f_75, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.17/3.85  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 10.17/3.85  tff(f_169, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 10.17/3.85  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 10.17/3.85  tff(f_93, axiom, (![A]: (v1_zfmisc_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_zfmisc_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_1)).
% 10.17/3.85  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.17/3.85  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.17/3.85  tff(f_148, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tex_2)).
% 10.17/3.85  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 10.17/3.85  tff(f_83, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 10.17/3.85  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.17/3.85  tff(c_62, plain, (v1_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.17/3.85  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.17/3.85  tff(c_90, plain, (![B_67, A_68]: (l1_pre_topc(B_67) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.17/3.85  tff(c_99, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_68, c_90])).
% 10.17/3.85  tff(c_106, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_99])).
% 10.17/3.85  tff(c_44, plain, (![A_39]: (m1_pre_topc(A_39, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.17/3.85  tff(c_52, plain, (![B_49, A_43]: (u1_struct_0(B_49)='#skF_2'(A_43, B_49) | v1_tex_2(B_49, A_43) | ~m1_pre_topc(B_49, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_42, plain, (![B_38, A_36]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.17/3.85  tff(c_14755, plain, (![B_645, A_646]: (v1_subset_1(u1_struct_0(B_645), u1_struct_0(A_646)) | ~m1_subset_1(u1_struct_0(B_645), k1_zfmisc_1(u1_struct_0(A_646))) | ~v1_tex_2(B_645, A_646) | ~m1_pre_topc(B_645, A_646) | ~l1_pre_topc(A_646))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_16555, plain, (![B_697, A_698]: (v1_subset_1(u1_struct_0(B_697), u1_struct_0(A_698)) | ~v1_tex_2(B_697, A_698) | ~m1_pre_topc(B_697, A_698) | ~l1_pre_topc(A_698))), inference(resolution, [status(thm)], [c_42, c_14755])).
% 10.17/3.85  tff(c_14, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.17/3.85  tff(c_26, plain, (![A_20]: (~v1_subset_1(k2_subset_1(A_20), A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.17/3.85  tff(c_71, plain, (![A_20]: (~v1_subset_1(A_20, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 10.17/3.85  tff(c_16622, plain, (![A_699]: (~v1_tex_2(A_699, A_699) | ~m1_pre_topc(A_699, A_699) | ~l1_pre_topc(A_699))), inference(resolution, [status(thm)], [c_16555, c_71])).
% 10.17/3.85  tff(c_16628, plain, (![A_700]: (u1_struct_0(A_700)='#skF_2'(A_700, A_700) | ~m1_pre_topc(A_700, A_700) | ~l1_pre_topc(A_700))), inference(resolution, [status(thm)], [c_52, c_16622])).
% 10.17/3.85  tff(c_16664, plain, (![A_701]: (u1_struct_0(A_701)='#skF_2'(A_701, A_701) | ~l1_pre_topc(A_701))), inference(resolution, [status(thm)], [c_44, c_16628])).
% 10.17/3.85  tff(c_16686, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_106, c_16664])).
% 10.17/3.85  tff(c_66, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.17/3.85  tff(c_307, plain, (![B_113, A_114]: (u1_struct_0(B_113)='#skF_2'(A_114, B_113) | v1_tex_2(B_113, A_114) | ~m1_pre_topc(B_113, A_114) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_60, plain, (~v1_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.17/3.85  tff(c_310, plain, (u1_struct_0('#skF_5')='#skF_2'('#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_307, c_60])).
% 10.17/3.85  tff(c_313, plain, (u1_struct_0('#skF_5')='#skF_2'('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_310])).
% 10.17/3.85  tff(c_64, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.17/3.85  tff(c_314, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_64])).
% 10.17/3.85  tff(c_12377, plain, (![A_565, B_566]: (m1_pre_topc(A_565, g1_pre_topc(u1_struct_0(B_566), u1_pre_topc(B_566))) | ~m1_pre_topc(A_565, B_566) | ~l1_pre_topc(B_566) | ~l1_pre_topc(A_565))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.17/3.85  tff(c_12392, plain, (![A_565]: (m1_pre_topc(A_565, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_565, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_565))), inference(superposition, [status(thm), theory('equality')], [c_314, c_12377])).
% 10.17/3.85  tff(c_13081, plain, (![A_598]: (m1_pre_topc(A_598, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_598, '#skF_4') | ~l1_pre_topc(A_598))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_12392])).
% 10.17/3.85  tff(c_96, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_90])).
% 10.17/3.85  tff(c_103, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_96])).
% 10.17/3.85  tff(c_241, plain, (![B_105, A_106]: (m1_pre_topc(B_105, A_106) | ~m1_pre_topc(B_105, g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.17/3.85  tff(c_244, plain, (![B_105]: (m1_pre_topc(B_105, '#skF_5') | ~m1_pre_topc(B_105, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_241])).
% 10.17/3.85  tff(c_250, plain, (![B_105]: (m1_pre_topc(B_105, '#skF_5') | ~m1_pre_topc(B_105, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_244])).
% 10.17/3.85  tff(c_354, plain, (![B_105]: (m1_pre_topc(B_105, '#skF_5') | ~m1_pre_topc(B_105, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_250])).
% 10.17/3.85  tff(c_13462, plain, (![A_604]: (m1_pre_topc(A_604, '#skF_5') | ~m1_pre_topc(A_604, '#skF_4') | ~l1_pre_topc(A_604))), inference(resolution, [status(thm)], [c_13081, c_354])).
% 10.17/3.85  tff(c_12978, plain, (![B_592, A_593]: (v1_subset_1(u1_struct_0(B_592), u1_struct_0(A_593)) | ~m1_subset_1(u1_struct_0(B_592), k1_zfmisc_1(u1_struct_0(A_593))) | ~v1_tex_2(B_592, A_593) | ~m1_pre_topc(B_592, A_593) | ~l1_pre_topc(A_593))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_13011, plain, (![B_594, A_595]: (v1_subset_1(u1_struct_0(B_594), u1_struct_0(A_595)) | ~v1_tex_2(B_594, A_595) | ~m1_pre_topc(B_594, A_595) | ~l1_pre_topc(A_595))), inference(resolution, [status(thm)], [c_42, c_12978])).
% 10.17/3.85  tff(c_13046, plain, (![A_596]: (~v1_tex_2(A_596, A_596) | ~m1_pre_topc(A_596, A_596) | ~l1_pre_topc(A_596))), inference(resolution, [status(thm)], [c_13011, c_71])).
% 10.17/3.85  tff(c_13052, plain, (![A_597]: (u1_struct_0(A_597)='#skF_2'(A_597, A_597) | ~m1_pre_topc(A_597, A_597) | ~l1_pre_topc(A_597))), inference(resolution, [status(thm)], [c_52, c_13046])).
% 10.17/3.85  tff(c_13136, plain, (![A_599]: (u1_struct_0(A_599)='#skF_2'(A_599, A_599) | ~l1_pre_topc(A_599))), inference(resolution, [status(thm)], [c_44, c_13052])).
% 10.17/3.85  tff(c_13153, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_106, c_13136])).
% 10.17/3.85  tff(c_334, plain, (![B_38]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc(B_38, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_42])).
% 10.17/3.85  tff(c_7771, plain, (![B_392]: (m1_subset_1(u1_struct_0(B_392), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc(B_392, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_334])).
% 10.17/3.85  tff(c_7789, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_313, c_7771])).
% 10.17/3.85  tff(c_7940, plain, (~m1_pre_topc('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_7789])).
% 10.17/3.85  tff(c_7943, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_44, c_7940])).
% 10.17/3.85  tff(c_7947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_7943])).
% 10.17/3.85  tff(c_7949, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_7789])).
% 10.17/3.85  tff(c_8388, plain, (![B_427, A_428]: (v1_subset_1(u1_struct_0(B_427), u1_struct_0(A_428)) | ~m1_subset_1(u1_struct_0(B_427), k1_zfmisc_1(u1_struct_0(A_428))) | ~v1_tex_2(B_427, A_428) | ~m1_pre_topc(B_427, A_428) | ~l1_pre_topc(A_428))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_8459, plain, (![B_431, A_432]: (v1_subset_1(u1_struct_0(B_431), u1_struct_0(A_432)) | ~v1_tex_2(B_431, A_432) | ~m1_pre_topc(B_431, A_432) | ~l1_pre_topc(A_432))), inference(resolution, [status(thm)], [c_42, c_8388])).
% 10.17/3.85  tff(c_8526, plain, (![A_434]: (~v1_tex_2(A_434, A_434) | ~m1_pre_topc(A_434, A_434) | ~l1_pre_topc(A_434))), inference(resolution, [status(thm)], [c_8459, c_71])).
% 10.17/3.85  tff(c_8532, plain, (![A_435]: (u1_struct_0(A_435)='#skF_2'(A_435, A_435) | ~m1_pre_topc(A_435, A_435) | ~l1_pre_topc(A_435))), inference(resolution, [status(thm)], [c_52, c_8526])).
% 10.17/3.85  tff(c_8581, plain, (![A_436]: (u1_struct_0(A_436)='#skF_2'(A_436, A_436) | ~l1_pre_topc(A_436))), inference(resolution, [status(thm)], [c_44, c_8532])).
% 10.17/3.85  tff(c_8594, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_106, c_8581])).
% 10.17/3.85  tff(c_8621, plain, (g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))=g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_314])).
% 10.17/3.85  tff(c_8006, plain, (![A_398, B_399]: (m1_pre_topc(A_398, g1_pre_topc(u1_struct_0(B_399), u1_pre_topc(B_399))) | ~m1_pre_topc(A_398, B_399) | ~l1_pre_topc(B_399) | ~l1_pre_topc(A_398))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.17/3.85  tff(c_8024, plain, (![A_398]: (m1_pre_topc(A_398, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_398, '#skF_5') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_398))), inference(superposition, [status(thm), theory('equality')], [c_313, c_8006])).
% 10.17/3.85  tff(c_8033, plain, (![A_398]: (m1_pre_topc(A_398, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_398, '#skF_5') | ~l1_pre_topc(A_398))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_8024])).
% 10.17/3.85  tff(c_12116, plain, (![A_553]: (m1_pre_topc(A_553, g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_553, '#skF_5') | ~l1_pre_topc(A_553))), inference(demodulation, [status(thm), theory('equality')], [c_8621, c_8033])).
% 10.17/3.85  tff(c_259, plain, (![B_108, A_109]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_108), u1_pre_topc(B_108)), A_109) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.17/3.85  tff(c_30, plain, (![B_26, A_24]: (l1_pre_topc(B_26) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.17/3.85  tff(c_283, plain, (![B_110, A_111]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_110), u1_pre_topc(B_110))) | ~m1_pre_topc(B_110, A_111) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_259, c_30])).
% 10.17/3.85  tff(c_293, plain, (![A_39]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_39), u1_pre_topc(A_39))) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_44, c_283])).
% 10.17/3.85  tff(c_318, plain, (l1_pre_topc(g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_313, c_293])).
% 10.17/3.85  tff(c_341, plain, (l1_pre_topc(g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_318])).
% 10.17/3.85  tff(c_8866, plain, (l1_pre_topc(g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8621, c_341])).
% 10.17/3.85  tff(c_8597, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_8581])).
% 10.17/3.85  tff(c_8404, plain, (![B_38, A_36]: (v1_subset_1(u1_struct_0(B_38), u1_struct_0(A_36)) | ~v1_tex_2(B_38, A_36) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_42, c_8388])).
% 10.17/3.85  tff(c_8755, plain, (![B_38]: (v1_subset_1(u1_struct_0(B_38), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2(B_38, '#skF_3') | ~m1_pre_topc(B_38, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8597, c_8404])).
% 10.17/3.85  tff(c_9933, plain, (![B_477]: (v1_subset_1(u1_struct_0(B_477), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2(B_477, '#skF_3') | ~m1_pre_topc(B_477, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8755])).
% 10.17/3.85  tff(c_9941, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8594, c_9933])).
% 10.17/3.85  tff(c_9950, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_9941])).
% 10.17/3.85  tff(c_175, plain, (![B_95, A_96]: (m1_subset_1(u1_struct_0(B_95), k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.17/3.85  tff(c_22, plain, (![B_16, A_14]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.17/3.85  tff(c_193, plain, (![B_95, A_96]: (v1_xboole_0(u1_struct_0(B_95)) | ~v1_xboole_0(u1_struct_0(A_96)) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_175, c_22])).
% 10.17/3.85  tff(c_328, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_5')) | ~m1_pre_topc(B_95, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_193])).
% 10.17/3.85  tff(c_347, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_5')) | ~m1_pre_topc(B_95, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_328])).
% 10.17/3.85  tff(c_7797, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_347])).
% 10.17/3.85  tff(c_8688, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~m1_pre_topc(B_95, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8594, c_193])).
% 10.17/3.85  tff(c_8733, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~m1_pre_topc(B_95, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_8688])).
% 10.17/3.85  tff(c_9617, plain, (~v1_xboole_0('#skF_2'('#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_8733])).
% 10.17/3.85  tff(c_1154, plain, (![B_162, A_163]: (v1_subset_1(u1_struct_0(B_162), u1_struct_0(A_163)) | ~m1_subset_1(u1_struct_0(B_162), k1_zfmisc_1(u1_struct_0(A_163))) | ~v1_tex_2(B_162, A_163) | ~m1_pre_topc(B_162, A_163) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_1199, plain, (![B_166, A_167]: (v1_subset_1(u1_struct_0(B_166), u1_struct_0(A_167)) | ~v1_tex_2(B_166, A_167) | ~m1_pre_topc(B_166, A_167) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_42, c_1154])).
% 10.17/3.85  tff(c_1233, plain, (![A_170]: (~v1_tex_2(A_170, A_170) | ~m1_pre_topc(A_170, A_170) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_1199, c_71])).
% 10.17/3.85  tff(c_1239, plain, (![A_171]: (u1_struct_0(A_171)='#skF_2'(A_171, A_171) | ~m1_pre_topc(A_171, A_171) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_52, c_1233])).
% 10.17/3.85  tff(c_1320, plain, (![A_172]: (u1_struct_0(A_172)='#skF_2'(A_172, A_172) | ~l1_pre_topc(A_172))), inference(resolution, [status(thm)], [c_44, c_1239])).
% 10.17/3.85  tff(c_1333, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_106, c_1320])).
% 10.17/3.85  tff(c_1336, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_1320])).
% 10.17/3.85  tff(c_1555, plain, (![B_38]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~m1_pre_topc(B_38, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_42])).
% 10.17/3.85  tff(c_1743, plain, (![B_180]: (m1_subset_1(u1_struct_0(B_180), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~m1_pre_topc(B_180, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1555])).
% 10.17/3.85  tff(c_1772, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1333, c_1743])).
% 10.17/3.85  tff(c_1786, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1772])).
% 10.17/3.85  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1('#skF_1'(A_11, B_12), A_11) | B_12=A_11 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.17/3.85  tff(c_1026, plain, (![A_151, B_152]: (m1_subset_1('#skF_2'(A_151, B_152), k1_zfmisc_1(u1_struct_0(A_151))) | v1_tex_2(B_152, A_151) | ~m1_pre_topc(B_152, A_151) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_56, plain, (![B_54, A_53]: (v1_subset_1(B_54, A_53) | B_54=A_53 | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.17/3.85  tff(c_2713, plain, (![A_212, B_213]: (v1_subset_1('#skF_2'(A_212, B_213), u1_struct_0(A_212)) | u1_struct_0(A_212)='#skF_2'(A_212, B_213) | v1_tex_2(B_213, A_212) | ~m1_pre_topc(B_213, A_212) | ~l1_pre_topc(A_212))), inference(resolution, [status(thm)], [c_1026, c_56])).
% 10.17/3.85  tff(c_50, plain, (![A_43, B_49]: (~v1_subset_1('#skF_2'(A_43, B_49), u1_struct_0(A_43)) | v1_tex_2(B_49, A_43) | ~m1_pre_topc(B_49, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_4482, plain, (![A_241, B_242]: (u1_struct_0(A_241)='#skF_2'(A_241, B_242) | v1_tex_2(B_242, A_241) | ~m1_pre_topc(B_242, A_241) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_2713, c_50])).
% 10.17/3.85  tff(c_4498, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4482, c_60])).
% 10.17/3.85  tff(c_4511, plain, ('#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1336, c_4498])).
% 10.17/3.85  tff(c_385, plain, (![B_115]: (m1_subset_1(u1_struct_0(B_115), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc(B_115, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_334])).
% 10.17/3.85  tff(c_403, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_313, c_385])).
% 10.17/3.85  tff(c_537, plain, (~m1_pre_topc('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_403])).
% 10.17/3.85  tff(c_568, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_44, c_537])).
% 10.17/3.85  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_568])).
% 10.17/3.85  tff(c_574, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_403])).
% 10.17/3.85  tff(c_825, plain, (![A_143, B_144]: (m1_pre_topc(A_143, g1_pre_topc(u1_struct_0(B_144), u1_pre_topc(B_144))) | ~m1_pre_topc(A_143, B_144) | ~l1_pre_topc(B_144) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.17/3.85  tff(c_843, plain, (![A_143]: (m1_pre_topc(A_143, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_143, '#skF_5') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_143))), inference(superposition, [status(thm), theory('equality')], [c_313, c_825])).
% 10.17/3.85  tff(c_905, plain, (![A_147]: (m1_pre_topc(A_147, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_147, '#skF_5') | ~l1_pre_topc(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_843])).
% 10.17/3.85  tff(c_32, plain, (![B_29, A_27]: (m1_pre_topc(B_29, A_27) | ~m1_pre_topc(B_29, g1_pre_topc(u1_struct_0(A_27), u1_pre_topc(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.17/3.85  tff(c_367, plain, (![B_29]: (m1_pre_topc(B_29, '#skF_4') | ~m1_pre_topc(B_29, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_32])).
% 10.17/3.85  tff(c_376, plain, (![B_29]: (m1_pre_topc(B_29, '#skF_4') | ~m1_pre_topc(B_29, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_367])).
% 10.17/3.85  tff(c_935, plain, (![A_148]: (m1_pre_topc(A_148, '#skF_4') | ~m1_pre_topc(A_148, '#skF_5') | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_905, c_376])).
% 10.17/3.85  tff(c_945, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_574, c_935])).
% 10.17/3.85  tff(c_967, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_945])).
% 10.17/3.85  tff(c_4, plain, (![A_3]: (v1_zfmisc_1(A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.17/3.85  tff(c_28, plain, (![B_23, A_21]: (v1_zfmisc_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_21)) | ~v1_zfmisc_1(A_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.17/3.85  tff(c_194, plain, (![B_95, A_96]: (v1_zfmisc_1(u1_struct_0(B_95)) | ~v1_zfmisc_1(u1_struct_0(A_96)) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_175, c_28])).
% 10.17/3.85  tff(c_326, plain, (![B_95]: (v1_zfmisc_1(u1_struct_0(B_95)) | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_5')) | ~m1_pre_topc(B_95, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_194])).
% 10.17/3.85  tff(c_345, plain, (![B_95]: (v1_zfmisc_1(u1_struct_0(B_95)) | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_5')) | ~m1_pre_topc(B_95, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_326])).
% 10.17/3.85  tff(c_380, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_345])).
% 10.17/3.85  tff(c_384, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_380])).
% 10.17/3.85  tff(c_732, plain, (![A_134]: (m1_subset_1('#skF_2'('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_pre_topc('#skF_5', A_134) | ~l1_pre_topc(A_134))), inference(superposition, [status(thm), theory('equality')], [c_313, c_42])).
% 10.17/3.85  tff(c_8, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.17/3.85  tff(c_142, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.17/3.85  tff(c_145, plain, (![B_5, A_84, A_4]: (r2_hidden(B_5, A_84) | ~m1_subset_1(A_4, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(resolution, [status(thm)], [c_8, c_142])).
% 10.17/3.85  tff(c_734, plain, (![B_5, A_134]: (r2_hidden(B_5, u1_struct_0(A_134)) | ~m1_subset_1(B_5, '#skF_2'('#skF_3', '#skF_5')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_5')) | ~m1_pre_topc('#skF_5', A_134) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_732, c_145])).
% 10.17/3.85  tff(c_761, plain, (![B_5, A_134]: (r2_hidden(B_5, u1_struct_0(A_134)) | ~m1_subset_1(B_5, '#skF_2'('#skF_3', '#skF_5')) | ~m1_pre_topc('#skF_5', A_134) | ~l1_pre_topc(A_134))), inference(negUnitSimplification, [status(thm)], [c_384, c_734])).
% 10.17/3.85  tff(c_1359, plain, (![B_5]: (r2_hidden(B_5, '#skF_2'('#skF_4', '#skF_4')) | ~m1_subset_1(B_5, '#skF_2'('#skF_3', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1333, c_761])).
% 10.17/3.85  tff(c_2052, plain, (![B_185]: (r2_hidden(B_185, '#skF_2'('#skF_4', '#skF_4')) | ~m1_subset_1(B_185, '#skF_2'('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_967, c_1359])).
% 10.17/3.85  tff(c_18, plain, (![A_11, B_12]: (~r2_hidden('#skF_1'(A_11, B_12), B_12) | B_12=A_11 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.17/3.85  tff(c_2062, plain, (![A_11]: (A_11='#skF_2'('#skF_4', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1(A_11)) | ~m1_subset_1('#skF_1'(A_11, '#skF_2'('#skF_4', '#skF_4')), '#skF_2'('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_2052, c_18])).
% 10.17/3.85  tff(c_7639, plain, (![A_386]: (A_386='#skF_2'('#skF_4', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1(A_386)) | ~m1_subset_1('#skF_1'(A_386, '#skF_2'('#skF_4', '#skF_4')), '#skF_2'('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4511, c_2062])).
% 10.17/3.85  tff(c_7646, plain, ('#skF_2'('#skF_3', '#skF_3')='#skF_2'('#skF_4', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_20, c_7639])).
% 10.17/3.85  tff(c_7653, plain, ('#skF_2'('#skF_3', '#skF_3')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_7646])).
% 10.17/3.85  tff(c_4418, plain, (![A_239, B_240]: (u1_struct_0(A_239)='#skF_2'(A_239, B_240) | v1_tex_2(B_240, A_239) | ~m1_pre_topc(B_240, A_239) | ~l1_pre_topc(A_239))), inference(resolution, [status(thm)], [c_2713, c_50])).
% 10.17/3.85  tff(c_1170, plain, (![B_38, A_36]: (v1_subset_1(u1_struct_0(B_38), u1_struct_0(A_36)) | ~v1_tex_2(B_38, A_36) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_42, c_1154])).
% 10.17/3.85  tff(c_1356, plain, (![B_38]: (v1_subset_1(u1_struct_0(B_38), '#skF_2'('#skF_4', '#skF_4')) | ~v1_tex_2(B_38, '#skF_4') | ~m1_pre_topc(B_38, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1333, c_1170])).
% 10.17/3.85  tff(c_3641, plain, (![B_234]: (v1_subset_1(u1_struct_0(B_234), '#skF_2'('#skF_4', '#skF_4')) | ~v1_tex_2(B_234, '#skF_4') | ~m1_pre_topc(B_234, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1356])).
% 10.17/3.85  tff(c_3652, plain, (v1_subset_1('#skF_2'('#skF_3', '#skF_5'), '#skF_2'('#skF_4', '#skF_4')) | ~v1_tex_2('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_313, c_3641])).
% 10.17/3.85  tff(c_3658, plain, (v1_subset_1('#skF_2'('#skF_3', '#skF_5'), '#skF_2'('#skF_4', '#skF_4')) | ~v1_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_967, c_3652])).
% 10.17/3.85  tff(c_3665, plain, (~v1_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_3658])).
% 10.17/3.85  tff(c_4421, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4418, c_3665])).
% 10.17/3.85  tff(c_4440, plain, ('#skF_2'('#skF_4', '#skF_5')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_967, c_1333, c_4421])).
% 10.17/3.85  tff(c_3668, plain, (u1_struct_0('#skF_5')='#skF_2'('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_3665])).
% 10.17/3.85  tff(c_3671, plain, ('#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_967, c_313, c_3668])).
% 10.17/3.85  tff(c_1487, plain, (![B_38]: (v1_subset_1(u1_struct_0(B_38), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2(B_38, '#skF_3') | ~m1_pre_topc(B_38, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_1170])).
% 10.17/3.85  tff(c_2904, plain, (![B_220]: (v1_subset_1(u1_struct_0(B_220), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2(B_220, '#skF_3') | ~m1_pre_topc(B_220, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1487])).
% 10.17/3.85  tff(c_2912, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1333, c_2904])).
% 10.17/3.85  tff(c_2921, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_2912])).
% 10.17/3.85  tff(c_3375, plain, (![A_224, B_225]: (u1_struct_0(A_224)='#skF_2'(A_224, B_225) | v1_tex_2(B_225, A_224) | ~m1_pre_topc(B_225, A_224) | ~l1_pre_topc(A_224))), inference(resolution, [status(thm)], [c_2713, c_50])).
% 10.17/3.85  tff(c_3394, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_3375, c_60])).
% 10.17/3.85  tff(c_3410, plain, ('#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1336, c_3394])).
% 10.17/3.85  tff(c_840, plain, (![A_143]: (m1_pre_topc(A_143, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_143, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_143))), inference(superposition, [status(thm), theory('equality')], [c_314, c_825])).
% 10.17/3.85  tff(c_853, plain, (![A_145]: (m1_pre_topc(A_145, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_145, '#skF_4') | ~l1_pre_topc(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_840])).
% 10.17/3.85  tff(c_870, plain, (![A_145]: (m1_pre_topc(A_145, '#skF_5') | ~m1_pre_topc(A_145, '#skF_4') | ~l1_pre_topc(A_145))), inference(resolution, [status(thm)], [c_853, c_354])).
% 10.17/3.85  tff(c_349, plain, (![B_38]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc(B_38, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_334])).
% 10.17/3.85  tff(c_1405, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1333, c_349])).
% 10.17/3.85  tff(c_2425, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1405])).
% 10.17/3.85  tff(c_2428, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_870, c_2425])).
% 10.17/3.85  tff(c_2431, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2428])).
% 10.17/3.85  tff(c_2434, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2431])).
% 10.17/3.85  tff(c_2438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_2434])).
% 10.17/3.85  tff(c_2440, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1405])).
% 10.17/3.85  tff(c_1214, plain, (![B_166]: (v1_subset_1(u1_struct_0(B_166), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2(B_166, '#skF_5') | ~m1_pre_topc(B_166, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_1199])).
% 10.17/3.85  tff(c_2695, plain, (![B_211]: (v1_subset_1(u1_struct_0(B_211), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2(B_211, '#skF_5') | ~m1_pre_topc(B_211, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1214])).
% 10.17/3.85  tff(c_2703, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1333, c_2695])).
% 10.17/3.85  tff(c_2709, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2440, c_2703])).
% 10.17/3.85  tff(c_2748, plain, (~v1_tex_2('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2709])).
% 10.17/3.85  tff(c_2751, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2748])).
% 10.17/3.85  tff(c_2754, plain, ('#skF_2'('#skF_5', '#skF_4')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2440, c_1333, c_2751])).
% 10.17/3.85  tff(c_711, plain, (![A_131, B_132]: (~v1_subset_1('#skF_2'(A_131, B_132), u1_struct_0(A_131)) | v1_tex_2(B_132, A_131) | ~m1_pre_topc(B_132, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_714, plain, (![B_132]: (~v1_subset_1('#skF_2'('#skF_5', B_132), '#skF_2'('#skF_3', '#skF_5')) | v1_tex_2(B_132, '#skF_5') | ~m1_pre_topc(B_132, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_711])).
% 10.17/3.85  tff(c_716, plain, (![B_132]: (~v1_subset_1('#skF_2'('#skF_5', B_132), '#skF_2'('#skF_3', '#skF_5')) | v1_tex_2(B_132, '#skF_5') | ~m1_pre_topc(B_132, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_714])).
% 10.17/3.85  tff(c_2767, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | v1_tex_2('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2754, c_716])).
% 10.17/3.85  tff(c_2783, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | v1_tex_2('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2440, c_2767])).
% 10.17/3.85  tff(c_2784, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2748, c_2783])).
% 10.17/3.85  tff(c_3413, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3410, c_2784])).
% 10.17/3.85  tff(c_3441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2921, c_3413])).
% 10.17/3.85  tff(c_3442, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_2709])).
% 10.17/3.85  tff(c_3672, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3671, c_3442])).
% 10.17/3.85  tff(c_4464, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4440, c_3672])).
% 10.17/3.85  tff(c_4475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_4464])).
% 10.17/3.85  tff(c_4477, plain, (v1_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_3658])).
% 10.17/3.85  tff(c_4538, plain, (u1_struct_0('#skF_5')='#skF_2'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4511, c_313])).
% 10.17/3.85  tff(c_1431, plain, (![B_38]: (v1_subset_1(u1_struct_0(B_38), '#skF_2'('#skF_4', '#skF_4')) | ~v1_tex_2(B_38, '#skF_4') | ~m1_pre_topc(B_38, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1356])).
% 10.17/3.85  tff(c_4562, plain, (v1_subset_1('#skF_2'('#skF_3', '#skF_3'), '#skF_2'('#skF_4', '#skF_4')) | ~v1_tex_2('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4538, c_1431])).
% 10.17/3.85  tff(c_4681, plain, (v1_subset_1('#skF_2'('#skF_3', '#skF_3'), '#skF_2'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_967, c_4477, c_4562])).
% 10.17/3.85  tff(c_7714, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7653, c_4681])).
% 10.17/3.85  tff(c_7739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_7714])).
% 10.17/3.85  tff(c_7741, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_345])).
% 10.17/3.85  tff(c_8021, plain, (![A_398]: (m1_pre_topc(A_398, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_398, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_398))), inference(superposition, [status(thm), theory('equality')], [c_314, c_8006])).
% 10.17/3.85  tff(c_8307, plain, (![A_424]: (m1_pre_topc(A_424, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_pre_topc(A_424, '#skF_4') | ~l1_pre_topc(A_424))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_8021])).
% 10.17/3.85  tff(c_8333, plain, (![A_424]: (m1_pre_topc(A_424, '#skF_5') | ~m1_pre_topc(A_424, '#skF_4') | ~l1_pre_topc(A_424))), inference(resolution, [status(thm)], [c_8307, c_354])).
% 10.17/3.85  tff(c_7740, plain, (![B_95]: (v1_zfmisc_1(u1_struct_0(B_95)) | ~m1_pre_topc(B_95, '#skF_5'))), inference(splitRight, [status(thm)], [c_345])).
% 10.17/3.85  tff(c_8675, plain, (v1_zfmisc_1('#skF_2'('#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8594, c_7740])).
% 10.17/3.85  tff(c_8888, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_8675])).
% 10.17/3.85  tff(c_8946, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8333, c_8888])).
% 10.17/3.85  tff(c_8949, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_8946])).
% 10.17/3.85  tff(c_8952, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_44, c_8949])).
% 10.17/3.85  tff(c_8956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_8952])).
% 10.17/3.85  tff(c_8958, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_8675])).
% 10.17/3.85  tff(c_8672, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8594, c_349])).
% 10.17/3.85  tff(c_9805, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8958, c_8672])).
% 10.17/3.85  tff(c_46, plain, (![B_42, A_40]: (v1_xboole_0(B_42) | ~v1_subset_1(B_42, A_40) | ~m1_subset_1(B_42, k1_zfmisc_1(A_40)) | ~v1_zfmisc_1(A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.17/3.85  tff(c_9813, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_5')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_9805, c_46])).
% 10.17/3.85  tff(c_9835, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7741, c_9813])).
% 10.17/3.85  tff(c_9836, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_7797, c_9617, c_9835])).
% 10.17/3.85  tff(c_8474, plain, (![B_431]: (v1_subset_1(u1_struct_0(B_431), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2(B_431, '#skF_5') | ~m1_pre_topc(B_431, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_313, c_8459])).
% 10.17/3.85  tff(c_10121, plain, (![B_481]: (v1_subset_1(u1_struct_0(B_481), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2(B_481, '#skF_5') | ~m1_pre_topc(B_481, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_8474])).
% 10.17/3.85  tff(c_10132, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8594, c_10121])).
% 10.17/3.85  tff(c_10139, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | ~v1_tex_2('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8958, c_10132])).
% 10.17/3.85  tff(c_10140, plain, (~v1_tex_2('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_9836, c_10139])).
% 10.17/3.85  tff(c_10146, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_52, c_10140])).
% 10.17/3.85  tff(c_10149, plain, ('#skF_2'('#skF_5', '#skF_4')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_8958, c_8594, c_10146])).
% 10.17/3.85  tff(c_8255, plain, (![A_419, B_420]: (m1_subset_1('#skF_2'(A_419, B_420), k1_zfmisc_1(u1_struct_0(A_419))) | v1_tex_2(B_420, A_419) | ~m1_pre_topc(B_420, A_419) | ~l1_pre_topc(A_419))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_10360, plain, (![A_495, B_496]: (v1_subset_1('#skF_2'(A_495, B_496), u1_struct_0(A_495)) | u1_struct_0(A_495)='#skF_2'(A_495, B_496) | v1_tex_2(B_496, A_495) | ~m1_pre_topc(B_496, A_495) | ~l1_pre_topc(A_495))), inference(resolution, [status(thm)], [c_8255, c_56])).
% 10.17/3.85  tff(c_10368, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_2'('#skF_5', '#skF_4') | v1_tex_2('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10149, c_10360])).
% 10.17/3.85  tff(c_10384, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_5')) | '#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_4', '#skF_4') | v1_tex_2('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_8958, c_10149, c_313, c_313, c_10368])).
% 10.17/3.85  tff(c_10385, plain, ('#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_10140, c_9836, c_10384])).
% 10.17/3.85  tff(c_10429, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | v1_tex_2('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10385, c_50])).
% 10.17/3.85  tff(c_10439, plain, (v1_tex_2('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_9950, c_8597, c_10429])).
% 10.17/3.85  tff(c_10441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_10439])).
% 10.17/3.85  tff(c_10443, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_4'))), inference(splitRight, [status(thm)], [c_8733])).
% 10.17/3.85  tff(c_7863, plain, (![B_396]: (m1_pre_topc(B_396, '#skF_4') | ~m1_pre_topc(B_396, g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_367])).
% 10.17/3.85  tff(c_7875, plain, (m1_pre_topc(g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5')), '#skF_4') | ~l1_pre_topc(g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5')))), inference(resolution, [status(thm)], [c_44, c_7863])).
% 10.17/3.85  tff(c_7884, plain, (m1_pre_topc(g1_pre_topc('#skF_2'('#skF_3', '#skF_5'), u1_pre_topc('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_7875])).
% 10.17/3.85  tff(c_8860, plain, (m1_pre_topc(g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8621, c_7884])).
% 10.17/3.85  tff(c_10442, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~m1_pre_topc(B_95, '#skF_4'))), inference(splitRight, [status(thm)], [c_8733])).
% 10.17/3.85  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.17/3.85  tff(c_10477, plain, (![A_498]: (A_498='#skF_2'('#skF_4', '#skF_4') | ~v1_xboole_0(A_498))), inference(resolution, [status(thm)], [c_10443, c_2])).
% 10.17/3.85  tff(c_10523, plain, (![B_502]: (u1_struct_0(B_502)='#skF_2'('#skF_4', '#skF_4') | ~m1_pre_topc(B_502, '#skF_4'))), inference(resolution, [status(thm)], [c_10442, c_10477])).
% 10.17/3.85  tff(c_10549, plain, (u1_struct_0(g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4')))='#skF_2'('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_8860, c_10523])).
% 10.17/3.85  tff(c_8158, plain, (![A_411]: (m1_subset_1('#skF_2'('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0(A_411))) | ~m1_pre_topc('#skF_5', A_411) | ~l1_pre_topc(A_411))), inference(superposition, [status(thm), theory('equality')], [c_313, c_42])).
% 10.17/3.85  tff(c_8172, plain, (![A_411]: (v1_xboole_0('#skF_2'('#skF_3', '#skF_5')) | ~v1_xboole_0(u1_struct_0(A_411)) | ~m1_pre_topc('#skF_5', A_411) | ~l1_pre_topc(A_411))), inference(resolution, [status(thm)], [c_8158, c_22])).
% 10.17/3.85  tff(c_8192, plain, (![A_411]: (~v1_xboole_0(u1_struct_0(A_411)) | ~m1_pre_topc('#skF_5', A_411) | ~l1_pre_topc(A_411))), inference(negUnitSimplification, [status(thm)], [c_7797, c_8172])).
% 10.17/3.85  tff(c_10747, plain, (~v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_5', g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10549, c_8192])).
% 10.17/3.85  tff(c_10826, plain, (~m1_pre_topc('#skF_5', g1_pre_topc('#skF_2'('#skF_4', '#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8866, c_10443, c_10747])).
% 10.17/3.85  tff(c_12143, plain, (~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12116, c_10826])).
% 10.17/3.85  tff(c_12185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_7949, c_12143])).
% 10.17/3.85  tff(c_12186, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~m1_pre_topc(B_95, '#skF_5'))), inference(splitRight, [status(thm)], [c_347])).
% 10.17/3.85  tff(c_13193, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13153, c_12186])).
% 10.17/3.85  tff(c_13415, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_13193])).
% 10.17/3.85  tff(c_13465, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_13462, c_13415])).
% 10.17/3.85  tff(c_13489, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_13465])).
% 10.17/3.85  tff(c_13573, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_44, c_13489])).
% 10.17/3.85  tff(c_13577, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_13573])).
% 10.17/3.85  tff(c_13578, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_4'))), inference(splitRight, [status(thm)], [c_13193])).
% 10.17/3.85  tff(c_13156, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_13136])).
% 10.17/3.85  tff(c_13579, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_13193])).
% 10.17/3.85  tff(c_12187, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_347])).
% 10.17/3.85  tff(c_12227, plain, (![A_557]: (A_557='#skF_2'('#skF_3', '#skF_5') | ~v1_xboole_0(A_557))), inference(resolution, [status(thm)], [c_12187, c_2])).
% 10.17/3.85  tff(c_12234, plain, (![B_95]: (u1_struct_0(B_95)='#skF_2'('#skF_3', '#skF_5') | ~m1_pre_topc(B_95, '#skF_5'))), inference(resolution, [status(thm)], [c_12186, c_12227])).
% 10.17/3.85  tff(c_13588, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_13579, c_12234])).
% 10.17/3.85  tff(c_13607, plain, ('#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13153, c_13588])).
% 10.17/3.85  tff(c_13663, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | v1_tex_2('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13607, c_50])).
% 10.17/3.85  tff(c_13670, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3')) | v1_tex_2('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_13156, c_13663])).
% 10.17/3.85  tff(c_13671, plain, (~v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_13670])).
% 10.17/3.85  tff(c_54, plain, (![A_43, B_49]: (m1_subset_1('#skF_2'(A_43, B_49), k1_zfmisc_1(u1_struct_0(A_43))) | v1_tex_2(B_49, A_43) | ~m1_pre_topc(B_49, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_13660, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_tex_2('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13607, c_54])).
% 10.17/3.85  tff(c_13667, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | v1_tex_2('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_13156, c_13660])).
% 10.17/3.85  tff(c_13668, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_13667])).
% 10.17/3.85  tff(c_13833, plain, (v1_subset_1('#skF_2'('#skF_4', '#skF_4'), '#skF_2'('#skF_3', '#skF_3')) | '#skF_2'('#skF_3', '#skF_3')='#skF_2'('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_13668, c_56])).
% 10.17/3.85  tff(c_13854, plain, ('#skF_2'('#skF_3', '#skF_3')='#skF_2'('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_13671, c_13833])).
% 10.17/3.85  tff(c_222, plain, (![B_101, A_102]: (v1_zfmisc_1(u1_struct_0(B_101)) | ~v1_zfmisc_1(u1_struct_0(A_102)) | ~m1_pre_topc(B_101, A_102) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_175, c_28])).
% 10.17/3.85  tff(c_227, plain, (![B_103, A_104]: (v1_zfmisc_1(u1_struct_0(B_103)) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104) | ~v1_xboole_0(u1_struct_0(A_104)))), inference(resolution, [status(thm)], [c_4, c_222])).
% 10.17/3.85  tff(c_231, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_3') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_227])).
% 10.17/3.85  tff(c_237, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_231])).
% 10.17/3.85  tff(c_252, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_237])).
% 10.17/3.85  tff(c_13251, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13156, c_252])).
% 10.17/3.85  tff(c_13866, plain, (~v1_xboole_0('#skF_2'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13854, c_13251])).
% 10.17/3.85  tff(c_13870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13578, c_13866])).
% 10.17/3.85  tff(c_13872, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_237])).
% 10.17/3.85  tff(c_13879, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~m1_pre_topc(B_95, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_13872, c_193])).
% 10.17/3.85  tff(c_13884, plain, (![B_95]: (v1_xboole_0(u1_struct_0(B_95)) | ~m1_pre_topc(B_95, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_13879])).
% 10.17/3.85  tff(c_16879, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16686, c_13884])).
% 10.17/3.85  tff(c_16934, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16879])).
% 10.17/3.85  tff(c_13926, plain, (![B_616]: (v1_xboole_0(u1_struct_0(B_616)) | ~m1_pre_topc(B_616, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_13879])).
% 10.17/3.85  tff(c_13885, plain, (![A_1]: (u1_struct_0('#skF_3')=A_1 | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_13872, c_2])).
% 10.17/3.85  tff(c_13953, plain, (![B_618]: (u1_struct_0(B_618)=u1_struct_0('#skF_3') | ~m1_pre_topc(B_618, '#skF_3'))), inference(resolution, [status(thm)], [c_13926, c_13885])).
% 10.17/3.85  tff(c_13983, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_13953])).
% 10.17/3.85  tff(c_13982, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_13953])).
% 10.17/3.85  tff(c_14036, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13983, c_13982])).
% 10.17/3.85  tff(c_14204, plain, (![B_624, A_625]: (u1_struct_0(B_624)='#skF_2'(A_625, B_624) | v1_tex_2(B_624, A_625) | ~m1_pre_topc(B_624, A_625) | ~l1_pre_topc(A_625))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.17/3.85  tff(c_14207, plain, (u1_struct_0('#skF_5')='#skF_2'('#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14204, c_60])).
% 10.17/3.85  tff(c_14210, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_14036, c_14207])).
% 10.17/3.85  tff(c_16813, plain, ('#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16686, c_14210])).
% 10.17/3.85  tff(c_16689, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_16664])).
% 10.17/3.85  tff(c_14215, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14210, c_13983])).
% 10.17/3.85  tff(c_16690, plain, ('#skF_2'('#skF_3', '#skF_5')='#skF_2'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16689, c_14215])).
% 10.17/3.85  tff(c_17201, plain, ('#skF_2'('#skF_3', '#skF_3')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16813, c_16690])).
% 10.17/3.85  tff(c_17260, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17201, c_16689])).
% 10.17/3.85  tff(c_24, plain, (![B_19, A_17]: (~v1_subset_1(B_19, A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.17/3.85  tff(c_192, plain, (![B_95, A_96]: (~v1_subset_1(u1_struct_0(B_95), u1_struct_0(A_96)) | ~v1_xboole_0(u1_struct_0(A_96)) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_175, c_24])).
% 10.17/3.85  tff(c_19125, plain, (![A_745, B_746]: (~v1_xboole_0(u1_struct_0(A_745)) | ~v1_tex_2(B_746, A_745) | ~m1_pre_topc(B_746, A_745) | ~l1_pre_topc(A_745))), inference(resolution, [status(thm)], [c_16555, c_192])).
% 10.17/3.85  tff(c_19133, plain, (![B_746]: (~v1_xboole_0('#skF_2'('#skF_4', '#skF_4')) | ~v1_tex_2(B_746, '#skF_3') | ~m1_pre_topc(B_746, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_17260, c_19125])).
% 10.17/3.85  tff(c_19167, plain, (![B_748]: (~v1_tex_2(B_748, '#skF_3') | ~m1_pre_topc(B_748, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_16934, c_19133])).
% 10.17/3.85  tff(c_19174, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_19167])).
% 10.17/3.85  tff(c_19181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_19174])).
% 10.17/3.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.17/3.85  
% 10.17/3.85  Inference rules
% 10.17/3.85  ----------------------
% 10.17/3.85  #Ref     : 0
% 10.17/3.85  #Sup     : 3944
% 10.17/3.85  #Fact    : 0
% 10.17/3.85  #Define  : 0
% 10.17/3.85  #Split   : 29
% 10.17/3.85  #Chain   : 0
% 10.17/3.85  #Close   : 0
% 10.17/3.85  
% 10.17/3.85  Ordering : KBO
% 10.17/3.85  
% 10.17/3.85  Simplification rules
% 10.17/3.85  ----------------------
% 10.17/3.85  #Subsume      : 1340
% 10.17/3.85  #Demod        : 4766
% 10.17/3.85  #Tautology    : 1006
% 10.17/3.85  #SimpNegUnit  : 400
% 10.17/3.85  #BackRed      : 411
% 10.17/3.85  
% 10.17/3.85  #Partial instantiations: 0
% 10.17/3.85  #Strategies tried      : 1
% 10.17/3.85  
% 10.17/3.85  Timing (in seconds)
% 10.17/3.85  ----------------------
% 10.17/3.85  Preprocessing        : 0.37
% 10.17/3.85  Parsing              : 0.18
% 10.17/3.85  CNF conversion       : 0.03
% 10.17/3.85  Main loop            : 2.65
% 10.17/3.85  Inferencing          : 0.80
% 10.17/3.85  Reduction            : 0.99
% 10.17/3.85  Demodulation         : 0.70
% 10.17/3.85  BG Simplification    : 0.08
% 10.17/3.85  Subsumption          : 0.59
% 10.17/3.85  Abstraction          : 0.11
% 10.17/3.85  MUC search           : 0.00
% 10.17/3.85  Cooper               : 0.00
% 10.17/3.85  Total                : 3.12
% 10.17/3.85  Index Insertion      : 0.00
% 10.17/3.85  Index Deletion       : 0.00
% 10.17/3.85  Index Matching       : 0.00
% 10.17/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
