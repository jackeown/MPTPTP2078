%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:55 EST 2020

% Result     : Theorem 9.71s
% Output     : CNFRefutation 9.88s
% Verified   : 
% Statistics : Number of formulae       :  193 (1200 expanded)
%              Number of leaves         :   45 ( 425 expanded)
%              Depth                    :   28
%              Number of atoms          :  482 (3562 expanded)
%              Number of equality atoms :   29 ( 123 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_149,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_181,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_11583,plain,(
    ! [A_546,B_547] :
      ( m1_pre_topc('#skF_3'(A_546,B_547),A_546)
      | ~ m1_subset_1(B_547,k1_zfmisc_1(u1_struct_0(A_546)))
      | v1_xboole_0(B_547)
      | ~ l1_pre_topc(A_546)
      | v2_struct_0(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_11608,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_11583])).

tff(c_11624,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11608])).

tff(c_11625,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_11624])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_11631,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_11625,c_24])).

tff(c_11638,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11631])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11407,plain,(
    ! [A_531,B_532] :
      ( ~ v2_struct_0('#skF_3'(A_531,B_532))
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0(A_531)))
      | v1_xboole_0(B_532)
      | ~ l1_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_11434,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_11407])).

tff(c_11445,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11434])).

tff(c_11446,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_11445])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_38,plain,(
    ! [B_28,A_26] :
      ( v2_tdlat_3(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_11628,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11625,c_38])).

tff(c_11634,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_11628])).

tff(c_11635,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_11634])).

tff(c_30,plain,(
    ! [A_24] :
      ( v2_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_11642,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_11635,c_30])).

tff(c_11658,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11638,c_11642])).

tff(c_34,plain,(
    ! [A_25] :
      ( v7_struct_0(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_77,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_78,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_74])).

tff(c_553,plain,(
    ! [A_130,B_131] :
      ( u1_struct_0('#skF_3'(A_130,B_131)) = B_131
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | v1_xboole_0(B_131)
      | ~ l1_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_580,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_553])).

tff(c_591,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_580])).

tff(c_592,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_591])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k1_tarski(A_65),k1_zfmisc_1(B_66))
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tarski(A_65),B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_115,c_18])).

tff(c_218,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(A_90,B_89)
      | ~ v1_zfmisc_1(B_89)
      | v1_xboole_0(B_89)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_230,plain,(
    ! [A_65,B_66] :
      ( k1_tarski(A_65) = B_66
      | ~ v1_zfmisc_1(B_66)
      | v1_xboole_0(B_66)
      | v1_xboole_0(k1_tarski(A_65))
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_119,c_218])).

tff(c_262,plain,(
    ! [A_94,B_95] :
      ( k1_tarski(A_94) = B_95
      | ~ v1_zfmisc_1(B_95)
      | v1_xboole_0(B_95)
      | ~ r2_hidden(A_94,B_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_230])).

tff(c_274,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_262])).

tff(c_122,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72),A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,(
    ! [A_71] : r1_tarski(A_71,A_71) ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_136,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(A_84),B_85)
      | ~ r1_tarski(A_84,B_85)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_613,plain,(
    ! [A_132,B_133,B_134] :
      ( r2_hidden('#skF_1'(A_132),B_133)
      | ~ r1_tarski(B_134,B_133)
      | ~ r1_tarski(A_132,B_134)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_1335,plain,(
    ! [A_193,B_194,A_195] :
      ( r2_hidden('#skF_1'(A_193),B_194)
      | ~ r1_tarski(A_193,k1_tarski(A_195))
      | v1_xboole_0(A_193)
      | ~ r2_hidden(A_195,B_194) ) ),
    inference(resolution,[status(thm)],[c_119,c_613])).

tff(c_1366,plain,(
    ! [A_195,B_194] :
      ( r2_hidden('#skF_1'(k1_tarski(A_195)),B_194)
      | v1_xboole_0(k1_tarski(A_195))
      | ~ r2_hidden(A_195,B_194) ) ),
    inference(resolution,[status(thm)],[c_133,c_1335])).

tff(c_1384,plain,(
    ! [A_196,B_197] :
      ( r2_hidden('#skF_1'(k1_tarski(A_196)),B_197)
      | ~ r2_hidden(A_196,B_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1366])).

tff(c_240,plain,(
    ! [A_65,B_66] :
      ( k1_tarski(A_65) = B_66
      | ~ v1_zfmisc_1(B_66)
      | v1_xboole_0(B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_230])).

tff(c_1758,plain,(
    ! [A_218,B_219] :
      ( k1_tarski('#skF_1'(k1_tarski(A_218))) = B_219
      | ~ v1_zfmisc_1(B_219)
      | v1_xboole_0(B_219)
      | ~ r2_hidden(A_218,B_219) ) ),
    inference(resolution,[status(thm)],[c_1384,c_240])).

tff(c_1806,plain,(
    ! [A_222] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_222)))) = A_222
      | ~ v1_zfmisc_1(A_222)
      | v1_xboole_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_4,c_1758])).

tff(c_1380,plain,(
    ! [A_195,B_194] :
      ( r2_hidden('#skF_1'(k1_tarski(A_195)),B_194)
      | ~ r2_hidden(A_195,B_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1366])).

tff(c_9622,plain,(
    ! [A_435,B_436] :
      ( r2_hidden('#skF_1'(A_435),B_436)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_435))),B_436)
      | ~ v1_zfmisc_1(A_435)
      | v1_xboole_0(A_435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1806,c_1380])).

tff(c_9686,plain,(
    ! [A_435] :
      ( r2_hidden('#skF_1'(A_435),k1_tarski('#skF_1'(A_435)))
      | ~ v1_zfmisc_1(A_435)
      | v1_xboole_0(A_435)
      | v1_xboole_0(k1_tarski('#skF_1'(A_435))) ) ),
    inference(resolution,[status(thm)],[c_4,c_9622])).

tff(c_9719,plain,(
    ! [A_437] :
      ( r2_hidden('#skF_1'(A_437),k1_tarski('#skF_1'(A_437)))
      | ~ v1_zfmisc_1(A_437)
      | v1_xboole_0(A_437) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_9686])).

tff(c_1369,plain,(
    ! [A_65,B_194,A_195] :
      ( r2_hidden('#skF_1'(k1_tarski(A_65)),B_194)
      | v1_xboole_0(k1_tarski(A_65))
      | ~ r2_hidden(A_195,B_194)
      | ~ r2_hidden(A_65,k1_tarski(A_195)) ) ),
    inference(resolution,[status(thm)],[c_119,c_1335])).

tff(c_1736,plain,(
    ! [A_215,B_216,A_217] :
      ( r2_hidden('#skF_1'(k1_tarski(A_215)),B_216)
      | ~ r2_hidden(A_217,B_216)
      | ~ r2_hidden(A_215,k1_tarski(A_217)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1369])).

tff(c_1757,plain,(
    ! [A_215,A_1] :
      ( r2_hidden('#skF_1'(k1_tarski(A_215)),A_1)
      | ~ r2_hidden(A_215,k1_tarski('#skF_1'(A_1)))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_1736])).

tff(c_97,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_97])).

tff(c_1503,plain,(
    ! [A_203,B_204,B_205] :
      ( r2_hidden('#skF_1'(k1_tarski(A_203)),B_204)
      | ~ r1_tarski(B_205,B_204)
      | ~ r2_hidden(A_203,B_205) ) ),
    inference(resolution,[status(thm)],[c_1384,c_6])).

tff(c_1542,plain,(
    ! [A_203] :
      ( r2_hidden('#skF_1'(k1_tarski(A_203)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_203,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_101,c_1503])).

tff(c_3364,plain,(
    ! [A_285,B_286] :
      ( r1_tarski(A_285,B_286)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_285))),B_286)
      | ~ v1_zfmisc_1(A_285)
      | v1_xboole_0(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1806,c_119])).

tff(c_3618,plain,(
    ! [A_292] :
      ( r1_tarski(A_292,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_292)
      | v1_xboole_0(A_292)
      | ~ r2_hidden('#skF_1'(A_292),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1542,c_3364])).

tff(c_3634,plain,(
    ! [A_215] :
      ( r1_tarski(k1_tarski(A_215),u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_215))
      | v1_xboole_0(k1_tarski(A_215))
      | ~ r2_hidden(A_215,k1_tarski('#skF_1'('#skF_5')))
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1757,c_3618])).

tff(c_3655,plain,(
    ! [A_215] :
      ( r1_tarski(k1_tarski(A_215),u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_215))
      | ~ r2_hidden(A_215,k1_tarski('#skF_1'('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_12,c_3634])).

tff(c_9758,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_9719,c_3655])).

tff(c_9828,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9758])).

tff(c_9829,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_9828])).

tff(c_9850,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_9829])).

tff(c_9924,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_9850])).

tff(c_9926,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_9924])).

tff(c_9928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_9926])).

tff(c_9929,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9829])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_587,plain,(
    ! [A_130,A_15] :
      ( u1_struct_0('#skF_3'(A_130,A_15)) = A_15
      | v1_xboole_0(A_15)
      | ~ l1_pre_topc(A_130)
      | v2_struct_0(A_130)
      | ~ r1_tarski(A_15,u1_struct_0(A_130)) ) ),
    inference(resolution,[status(thm)],[c_20,c_553])).

tff(c_9946,plain,
    ( u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5')))) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_9929,c_587])).

tff(c_9984,plain,
    ( u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5')))) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9946])).

tff(c_9985,plain,(
    u1_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5')))) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_12,c_9984])).

tff(c_10174,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_9985])).

tff(c_10281,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_592,c_10174])).

tff(c_10282,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_10281])).

tff(c_9718,plain,(
    ! [A_435] :
      ( r2_hidden('#skF_1'(A_435),k1_tarski('#skF_1'(A_435)))
      | ~ v1_zfmisc_1(A_435)
      | v1_xboole_0(A_435) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_9686])).

tff(c_10386,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10282,c_9718])).

tff(c_10581,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10386])).

tff(c_10582,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_10581])).

tff(c_1543,plain,(
    ! [A_206] :
      ( r2_hidden('#skF_1'(k1_tarski(A_206)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_206,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_101,c_1503])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1578,plain,(
    ! [A_207] :
      ( m1_subset_1('#skF_1'(k1_tarski(A_207)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_207,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1543,c_16])).

tff(c_1587,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_1),'#skF_5')
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_1578])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_185,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | ~ r1_tarski(A_87,B_86)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_200,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_185])).

tff(c_208,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_200])).

tff(c_638,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_1'(A_135),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_135,'#skF_5')
      | v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_101,c_613])).

tff(c_776,plain,(
    ! [A_146] :
      ( m1_subset_1('#skF_1'(A_146),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_146,'#skF_5')
      | v1_xboole_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_638,c_16])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_779,plain,(
    ! [A_146] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_146)) = k1_tarski('#skF_1'(A_146))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_146,'#skF_5')
      | v1_xboole_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_776,c_28])).

tff(c_782,plain,(
    ! [A_146] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_146)) = k1_tarski('#skF_1'(A_146))
      | ~ r1_tarski(A_146,'#skF_5')
      | v1_xboole_0(A_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_779])).

tff(c_1036,plain,(
    ! [A_169,B_170] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_169),B_170),A_169)
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1039,plain,(
    ! [A_146] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_146)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_146),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_146,'#skF_5')
      | v1_xboole_0(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_1036])).

tff(c_1048,plain,(
    ! [A_146] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_146)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_146),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_146,'#skF_5')
      | v1_xboole_0(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1039])).

tff(c_1049,plain,(
    ! [A_146] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_146)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_146),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_146,'#skF_5')
      | v1_xboole_0(A_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1048])).

tff(c_10563,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10282,c_1049])).

tff(c_10678,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_10563])).

tff(c_10679,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_77,c_10678])).

tff(c_10831,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5'),'#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1587,c_10679])).

tff(c_10840,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10582,c_10831])).

tff(c_10842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_10840])).

tff(c_10843,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_11997,plain,(
    ! [A_574,B_575] :
      ( u1_struct_0('#skF_3'(A_574,B_575)) = B_575
      | ~ m1_subset_1(B_575,k1_zfmisc_1(u1_struct_0(A_574)))
      | v1_xboole_0(B_575)
      | ~ l1_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12035,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_11997])).

tff(c_12052,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12035])).

tff(c_12053,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_12052])).

tff(c_26,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12071,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12053,c_26])).

tff(c_12089,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_10843,c_12071])).

tff(c_12091,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_12089])).

tff(c_12094,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_12091])).

tff(c_12097,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11638,c_11658,c_11635,c_12094])).

tff(c_12098,plain,(
    ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_11446,c_12097])).

tff(c_10890,plain,(
    ! [A_460,B_461] :
      ( r2_hidden('#skF_2'(A_460,B_461),A_460)
      | r1_tarski(A_460,B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10901,plain,(
    ! [A_460] : r1_tarski(A_460,A_460) ),
    inference(resolution,[status(thm)],[c_10890,c_8])).

tff(c_10844,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_10868,plain,(
    ! [A_450,B_451] :
      ( r1_tarski(A_450,B_451)
      | ~ m1_subset_1(A_450,k1_zfmisc_1(B_451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10881,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_10868])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10913,plain,(
    ! [C_468,B_469,A_470] :
      ( r2_hidden(C_468,B_469)
      | ~ r2_hidden(C_468,A_470)
      | ~ r1_tarski(A_470,B_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11078,plain,(
    ! [A_490,B_491,B_492] :
      ( r2_hidden('#skF_2'(A_490,B_491),B_492)
      | ~ r1_tarski(A_490,B_492)
      | r1_tarski(A_490,B_491) ) ),
    inference(resolution,[status(thm)],[c_10,c_10913])).

tff(c_15439,plain,(
    ! [A_697,B_698,B_699,B_700] :
      ( r2_hidden('#skF_2'(A_697,B_698),B_699)
      | ~ r1_tarski(B_700,B_699)
      | ~ r1_tarski(A_697,B_700)
      | r1_tarski(A_697,B_698) ) ),
    inference(resolution,[status(thm)],[c_11078,c_6])).

tff(c_15551,plain,(
    ! [A_702,B_703] :
      ( r2_hidden('#skF_2'(A_702,B_703),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_702,'#skF_5')
      | r1_tarski(A_702,B_703) ) ),
    inference(resolution,[status(thm)],[c_10881,c_15439])).

tff(c_15577,plain,(
    ! [A_702] :
      ( ~ r1_tarski(A_702,'#skF_5')
      | r1_tarski(A_702,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_15551,c_8])).

tff(c_12163,plain,(
    ! [B_578,A_579] :
      ( v1_tdlat_3(B_578)
      | ~ v2_tex_2(u1_struct_0(B_578),A_579)
      | ~ m1_subset_1(u1_struct_0(B_578),k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ m1_pre_topc(B_578,A_579)
      | v2_struct_0(B_578)
      | ~ l1_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_15663,plain,(
    ! [B_708,A_709] :
      ( v1_tdlat_3(B_708)
      | ~ v2_tex_2(u1_struct_0(B_708),A_709)
      | ~ m1_pre_topc(B_708,A_709)
      | v2_struct_0(B_708)
      | ~ l1_pre_topc(A_709)
      | v2_struct_0(A_709)
      | ~ r1_tarski(u1_struct_0(B_708),u1_struct_0(A_709)) ) ),
    inference(resolution,[status(thm)],[c_20,c_12163])).

tff(c_15667,plain,(
    ! [B_708] :
      ( v1_tdlat_3(B_708)
      | ~ v2_tex_2(u1_struct_0(B_708),'#skF_4')
      | ~ m1_pre_topc(B_708,'#skF_4')
      | v2_struct_0(B_708)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(u1_struct_0(B_708),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_15577,c_15663])).

tff(c_15713,plain,(
    ! [B_708] :
      ( v1_tdlat_3(B_708)
      | ~ v2_tex_2(u1_struct_0(B_708),'#skF_4')
      | ~ m1_pre_topc(B_708,'#skF_4')
      | v2_struct_0(B_708)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(u1_struct_0(B_708),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_15667])).

tff(c_15841,plain,(
    ! [B_713] :
      ( v1_tdlat_3(B_713)
      | ~ v2_tex_2(u1_struct_0(B_713),'#skF_4')
      | ~ m1_pre_topc(B_713,'#skF_4')
      | v2_struct_0(B_713)
      | ~ r1_tarski(u1_struct_0(B_713),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_15713])).

tff(c_15862,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ r1_tarski(u1_struct_0('#skF_3'('#skF_4','#skF_5')),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12053,c_15841])).

tff(c_15865,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10901,c_12053,c_11625,c_10844,c_15862])).

tff(c_15867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11446,c_12098,c_15865])).

tff(c_15868,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_12089])).

tff(c_15872,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_15868])).

tff(c_15876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11638,c_15872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.71/3.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.87  
% 9.71/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.71/3.88  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 9.71/3.88  
% 9.71/3.88  %Foreground sorts:
% 9.71/3.88  
% 9.71/3.88  
% 9.71/3.88  %Background operators:
% 9.71/3.88  
% 9.71/3.88  
% 9.71/3.88  %Foreground operators:
% 9.71/3.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.71/3.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.71/3.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.71/3.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.71/3.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.71/3.88  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 9.71/3.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.71/3.88  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 9.71/3.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.71/3.88  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.71/3.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.71/3.88  tff('#skF_5', type, '#skF_5': $i).
% 9.71/3.88  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.71/3.88  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.71/3.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.71/3.88  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.71/3.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.71/3.88  tff('#skF_4', type, '#skF_4': $i).
% 9.71/3.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.71/3.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.71/3.88  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 9.71/3.88  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.71/3.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.71/3.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.71/3.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.71/3.88  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 9.71/3.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.71/3.88  
% 9.88/3.90  tff(f_201, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 9.88/3.90  tff(f_136, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 9.88/3.90  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.88/3.90  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.88/3.90  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 9.88/3.90  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 9.88/3.90  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 9.88/3.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.88/3.90  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.88/3.90  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 9.88/3.90  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.88/3.90  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 9.88/3.90  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.88/3.90  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.88/3.90  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.88/3.90  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 9.88/3.90  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 9.88/3.90  tff(f_169, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 9.88/3.90  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_11583, plain, (![A_546, B_547]: (m1_pre_topc('#skF_3'(A_546, B_547), A_546) | ~m1_subset_1(B_547, k1_zfmisc_1(u1_struct_0(A_546))) | v1_xboole_0(B_547) | ~l1_pre_topc(A_546) | v2_struct_0(A_546))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.88/3.90  tff(c_11608, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_11583])).
% 9.88/3.90  tff(c_11624, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11608])).
% 9.88/3.90  tff(c_11625, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_11624])).
% 9.88/3.90  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.88/3.90  tff(c_11631, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_11625, c_24])).
% 9.88/3.90  tff(c_11638, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11631])).
% 9.88/3.90  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.88/3.90  tff(c_11407, plain, (![A_531, B_532]: (~v2_struct_0('#skF_3'(A_531, B_532)) | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0(A_531))) | v1_xboole_0(B_532) | ~l1_pre_topc(A_531) | v2_struct_0(A_531))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.88/3.90  tff(c_11434, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_11407])).
% 9.88/3.90  tff(c_11445, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11434])).
% 9.88/3.90  tff(c_11446, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_11445])).
% 9.88/3.90  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_62, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_38, plain, (![B_28, A_26]: (v2_tdlat_3(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.88/3.90  tff(c_11628, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_11625, c_38])).
% 9.88/3.90  tff(c_11634, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_11628])).
% 9.88/3.90  tff(c_11635, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_11634])).
% 9.88/3.90  tff(c_30, plain, (![A_24]: (v2_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.88/3.90  tff(c_11642, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_11635, c_30])).
% 9.88/3.90  tff(c_11658, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11638, c_11642])).
% 9.88/3.90  tff(c_34, plain, (![A_25]: (v7_struct_0(A_25) | ~v2_tdlat_3(A_25) | ~v1_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.88/3.90  tff(c_68, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_77, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 9.88/3.90  tff(c_74, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.88/3.90  tff(c_78, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_77, c_74])).
% 9.88/3.90  tff(c_553, plain, (![A_130, B_131]: (u1_struct_0('#skF_3'(A_130, B_131))=B_131 | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | v1_xboole_0(B_131) | ~l1_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.88/3.90  tff(c_580, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_553])).
% 9.88/3.90  tff(c_591, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_580])).
% 9.88/3.90  tff(c_592, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_591])).
% 9.88/3.90  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.88/3.90  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.88/3.90  tff(c_115, plain, (![A_65, B_66]: (m1_subset_1(k1_tarski(A_65), k1_zfmisc_1(B_66)) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.88/3.90  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.88/3.90  tff(c_119, plain, (![A_65, B_66]: (r1_tarski(k1_tarski(A_65), B_66) | ~r2_hidden(A_65, B_66))), inference(resolution, [status(thm)], [c_115, c_18])).
% 9.88/3.90  tff(c_218, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(A_90, B_89) | ~v1_zfmisc_1(B_89) | v1_xboole_0(B_89) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.88/3.90  tff(c_230, plain, (![A_65, B_66]: (k1_tarski(A_65)=B_66 | ~v1_zfmisc_1(B_66) | v1_xboole_0(B_66) | v1_xboole_0(k1_tarski(A_65)) | ~r2_hidden(A_65, B_66))), inference(resolution, [status(thm)], [c_119, c_218])).
% 9.88/3.90  tff(c_262, plain, (![A_94, B_95]: (k1_tarski(A_94)=B_95 | ~v1_zfmisc_1(B_95) | v1_xboole_0(B_95) | ~r2_hidden(A_94, B_95))), inference(negUnitSimplification, [status(thm)], [c_12, c_230])).
% 9.88/3.90  tff(c_274, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_262])).
% 9.88/3.90  tff(c_122, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72), A_71) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.88/3.90  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.88/3.90  tff(c_133, plain, (![A_71]: (r1_tarski(A_71, A_71))), inference(resolution, [status(thm)], [c_122, c_8])).
% 9.88/3.90  tff(c_136, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.88/3.90  tff(c_173, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(A_84), B_85) | ~r1_tarski(A_84, B_85) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_4, c_136])).
% 9.88/3.90  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.88/3.90  tff(c_613, plain, (![A_132, B_133, B_134]: (r2_hidden('#skF_1'(A_132), B_133) | ~r1_tarski(B_134, B_133) | ~r1_tarski(A_132, B_134) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_173, c_6])).
% 9.88/3.90  tff(c_1335, plain, (![A_193, B_194, A_195]: (r2_hidden('#skF_1'(A_193), B_194) | ~r1_tarski(A_193, k1_tarski(A_195)) | v1_xboole_0(A_193) | ~r2_hidden(A_195, B_194))), inference(resolution, [status(thm)], [c_119, c_613])).
% 9.88/3.90  tff(c_1366, plain, (![A_195, B_194]: (r2_hidden('#skF_1'(k1_tarski(A_195)), B_194) | v1_xboole_0(k1_tarski(A_195)) | ~r2_hidden(A_195, B_194))), inference(resolution, [status(thm)], [c_133, c_1335])).
% 9.88/3.90  tff(c_1384, plain, (![A_196, B_197]: (r2_hidden('#skF_1'(k1_tarski(A_196)), B_197) | ~r2_hidden(A_196, B_197))), inference(negUnitSimplification, [status(thm)], [c_12, c_1366])).
% 9.88/3.90  tff(c_240, plain, (![A_65, B_66]: (k1_tarski(A_65)=B_66 | ~v1_zfmisc_1(B_66) | v1_xboole_0(B_66) | ~r2_hidden(A_65, B_66))), inference(negUnitSimplification, [status(thm)], [c_12, c_230])).
% 9.88/3.90  tff(c_1758, plain, (![A_218, B_219]: (k1_tarski('#skF_1'(k1_tarski(A_218)))=B_219 | ~v1_zfmisc_1(B_219) | v1_xboole_0(B_219) | ~r2_hidden(A_218, B_219))), inference(resolution, [status(thm)], [c_1384, c_240])).
% 9.88/3.90  tff(c_1806, plain, (![A_222]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_222))))=A_222 | ~v1_zfmisc_1(A_222) | v1_xboole_0(A_222))), inference(resolution, [status(thm)], [c_4, c_1758])).
% 9.88/3.90  tff(c_1380, plain, (![A_195, B_194]: (r2_hidden('#skF_1'(k1_tarski(A_195)), B_194) | ~r2_hidden(A_195, B_194))), inference(negUnitSimplification, [status(thm)], [c_12, c_1366])).
% 9.88/3.90  tff(c_9622, plain, (![A_435, B_436]: (r2_hidden('#skF_1'(A_435), B_436) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_435))), B_436) | ~v1_zfmisc_1(A_435) | v1_xboole_0(A_435))), inference(superposition, [status(thm), theory('equality')], [c_1806, c_1380])).
% 9.88/3.90  tff(c_9686, plain, (![A_435]: (r2_hidden('#skF_1'(A_435), k1_tarski('#skF_1'(A_435))) | ~v1_zfmisc_1(A_435) | v1_xboole_0(A_435) | v1_xboole_0(k1_tarski('#skF_1'(A_435))))), inference(resolution, [status(thm)], [c_4, c_9622])).
% 9.88/3.90  tff(c_9719, plain, (![A_437]: (r2_hidden('#skF_1'(A_437), k1_tarski('#skF_1'(A_437))) | ~v1_zfmisc_1(A_437) | v1_xboole_0(A_437))), inference(negUnitSimplification, [status(thm)], [c_12, c_9686])).
% 9.88/3.90  tff(c_1369, plain, (![A_65, B_194, A_195]: (r2_hidden('#skF_1'(k1_tarski(A_65)), B_194) | v1_xboole_0(k1_tarski(A_65)) | ~r2_hidden(A_195, B_194) | ~r2_hidden(A_65, k1_tarski(A_195)))), inference(resolution, [status(thm)], [c_119, c_1335])).
% 9.88/3.90  tff(c_1736, plain, (![A_215, B_216, A_217]: (r2_hidden('#skF_1'(k1_tarski(A_215)), B_216) | ~r2_hidden(A_217, B_216) | ~r2_hidden(A_215, k1_tarski(A_217)))), inference(negUnitSimplification, [status(thm)], [c_12, c_1369])).
% 9.88/3.90  tff(c_1757, plain, (![A_215, A_1]: (r2_hidden('#skF_1'(k1_tarski(A_215)), A_1) | ~r2_hidden(A_215, k1_tarski('#skF_1'(A_1))) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_1736])).
% 9.88/3.90  tff(c_97, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.88/3.90  tff(c_101, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_97])).
% 9.88/3.90  tff(c_1503, plain, (![A_203, B_204, B_205]: (r2_hidden('#skF_1'(k1_tarski(A_203)), B_204) | ~r1_tarski(B_205, B_204) | ~r2_hidden(A_203, B_205))), inference(resolution, [status(thm)], [c_1384, c_6])).
% 9.88/3.90  tff(c_1542, plain, (![A_203]: (r2_hidden('#skF_1'(k1_tarski(A_203)), u1_struct_0('#skF_4')) | ~r2_hidden(A_203, '#skF_5'))), inference(resolution, [status(thm)], [c_101, c_1503])).
% 9.88/3.90  tff(c_3364, plain, (![A_285, B_286]: (r1_tarski(A_285, B_286) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_285))), B_286) | ~v1_zfmisc_1(A_285) | v1_xboole_0(A_285))), inference(superposition, [status(thm), theory('equality')], [c_1806, c_119])).
% 9.88/3.90  tff(c_3618, plain, (![A_292]: (r1_tarski(A_292, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_292) | v1_xboole_0(A_292) | ~r2_hidden('#skF_1'(A_292), '#skF_5'))), inference(resolution, [status(thm)], [c_1542, c_3364])).
% 9.88/3.90  tff(c_3634, plain, (![A_215]: (r1_tarski(k1_tarski(A_215), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_215)) | v1_xboole_0(k1_tarski(A_215)) | ~r2_hidden(A_215, k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1757, c_3618])).
% 9.88/3.90  tff(c_3655, plain, (![A_215]: (r1_tarski(k1_tarski(A_215), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_215)) | ~r2_hidden(A_215, k1_tarski('#skF_1'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_12, c_3634])).
% 9.88/3.90  tff(c_9758, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_9719, c_3655])).
% 9.88/3.90  tff(c_9828, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_9758])).
% 9.88/3.90  tff(c_9829, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_9828])).
% 9.88/3.90  tff(c_9850, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_9829])).
% 9.88/3.90  tff(c_9924, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_274, c_9850])).
% 9.88/3.90  tff(c_9926, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_9924])).
% 9.88/3.90  tff(c_9928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_9926])).
% 9.88/3.90  tff(c_9929, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_9829])).
% 9.88/3.90  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.88/3.90  tff(c_587, plain, (![A_130, A_15]: (u1_struct_0('#skF_3'(A_130, A_15))=A_15 | v1_xboole_0(A_15) | ~l1_pre_topc(A_130) | v2_struct_0(A_130) | ~r1_tarski(A_15, u1_struct_0(A_130)))), inference(resolution, [status(thm)], [c_20, c_553])).
% 9.88/3.90  tff(c_9946, plain, (u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5'))))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_9929, c_587])).
% 9.88/3.90  tff(c_9984, plain, (u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5'))))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_9946])).
% 9.88/3.90  tff(c_9985, plain, (u1_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5'))))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_12, c_9984])).
% 9.88/3.90  tff(c_10174, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_274, c_9985])).
% 9.88/3.90  tff(c_10281, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_592, c_10174])).
% 9.88/3.90  tff(c_10282, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_58, c_10281])).
% 9.88/3.90  tff(c_9718, plain, (![A_435]: (r2_hidden('#skF_1'(A_435), k1_tarski('#skF_1'(A_435))) | ~v1_zfmisc_1(A_435) | v1_xboole_0(A_435))), inference(negUnitSimplification, [status(thm)], [c_12, c_9686])).
% 9.88/3.90  tff(c_10386, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10282, c_9718])).
% 9.88/3.90  tff(c_10581, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10386])).
% 9.88/3.90  tff(c_10582, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_10581])).
% 9.88/3.90  tff(c_1543, plain, (![A_206]: (r2_hidden('#skF_1'(k1_tarski(A_206)), u1_struct_0('#skF_4')) | ~r2_hidden(A_206, '#skF_5'))), inference(resolution, [status(thm)], [c_101, c_1503])).
% 9.88/3.90  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.88/3.90  tff(c_1578, plain, (![A_207]: (m1_subset_1('#skF_1'(k1_tarski(A_207)), u1_struct_0('#skF_4')) | ~r2_hidden(A_207, '#skF_5'))), inference(resolution, [status(thm)], [c_1543, c_16])).
% 9.88/3.90  tff(c_1587, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_1), '#skF_5') | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_274, c_1578])).
% 9.88/3.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.88/3.90  tff(c_185, plain, (![B_86, A_87]: (~v1_xboole_0(B_86) | ~r1_tarski(A_87, B_86) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_173, c_2])).
% 9.88/3.90  tff(c_200, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_101, c_185])).
% 9.88/3.90  tff(c_208, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_200])).
% 9.88/3.90  tff(c_638, plain, (![A_135]: (r2_hidden('#skF_1'(A_135), u1_struct_0('#skF_4')) | ~r1_tarski(A_135, '#skF_5') | v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_101, c_613])).
% 9.88/3.90  tff(c_776, plain, (![A_146]: (m1_subset_1('#skF_1'(A_146), u1_struct_0('#skF_4')) | ~r1_tarski(A_146, '#skF_5') | v1_xboole_0(A_146))), inference(resolution, [status(thm)], [c_638, c_16])).
% 9.88/3.90  tff(c_28, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.88/3.90  tff(c_779, plain, (![A_146]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_146))=k1_tarski('#skF_1'(A_146)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_146, '#skF_5') | v1_xboole_0(A_146))), inference(resolution, [status(thm)], [c_776, c_28])).
% 9.88/3.90  tff(c_782, plain, (![A_146]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_146))=k1_tarski('#skF_1'(A_146)) | ~r1_tarski(A_146, '#skF_5') | v1_xboole_0(A_146))), inference(negUnitSimplification, [status(thm)], [c_208, c_779])).
% 9.88/3.90  tff(c_1036, plain, (![A_169, B_170]: (v2_tex_2(k6_domain_1(u1_struct_0(A_169), B_170), A_169) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.88/3.90  tff(c_1039, plain, (![A_146]: (v2_tex_2(k1_tarski('#skF_1'(A_146)), '#skF_4') | ~m1_subset_1('#skF_1'(A_146), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_146, '#skF_5') | v1_xboole_0(A_146))), inference(superposition, [status(thm), theory('equality')], [c_782, c_1036])).
% 9.88/3.90  tff(c_1048, plain, (![A_146]: (v2_tex_2(k1_tarski('#skF_1'(A_146)), '#skF_4') | ~m1_subset_1('#skF_1'(A_146), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_146, '#skF_5') | v1_xboole_0(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1039])).
% 9.88/3.90  tff(c_1049, plain, (![A_146]: (v2_tex_2(k1_tarski('#skF_1'(A_146)), '#skF_4') | ~m1_subset_1('#skF_1'(A_146), u1_struct_0('#skF_4')) | ~r1_tarski(A_146, '#skF_5') | v1_xboole_0(A_146))), inference(negUnitSimplification, [status(thm)], [c_66, c_1048])).
% 9.88/3.90  tff(c_10563, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10282, c_1049])).
% 9.88/3.90  tff(c_10678, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_10563])).
% 9.88/3.90  tff(c_10679, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_77, c_10678])).
% 9.88/3.90  tff(c_10831, plain, (~r2_hidden('#skF_1'('#skF_5'), '#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1587, c_10679])).
% 9.88/3.90  tff(c_10840, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10582, c_10831])).
% 9.88/3.90  tff(c_10842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_10840])).
% 9.88/3.90  tff(c_10843, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 9.88/3.90  tff(c_11997, plain, (![A_574, B_575]: (u1_struct_0('#skF_3'(A_574, B_575))=B_575 | ~m1_subset_1(B_575, k1_zfmisc_1(u1_struct_0(A_574))) | v1_xboole_0(B_575) | ~l1_pre_topc(A_574) | v2_struct_0(A_574))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.88/3.90  tff(c_12035, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_11997])).
% 9.88/3.90  tff(c_12052, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12035])).
% 9.88/3.90  tff(c_12053, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_12052])).
% 9.88/3.90  tff(c_26, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.88/3.90  tff(c_12071, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12053, c_26])).
% 9.88/3.90  tff(c_12089, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_10843, c_12071])).
% 9.88/3.90  tff(c_12091, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_12089])).
% 9.88/3.90  tff(c_12094, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_12091])).
% 9.88/3.90  tff(c_12097, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11638, c_11658, c_11635, c_12094])).
% 9.88/3.90  tff(c_12098, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_11446, c_12097])).
% 9.88/3.90  tff(c_10890, plain, (![A_460, B_461]: (r2_hidden('#skF_2'(A_460, B_461), A_460) | r1_tarski(A_460, B_461))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.88/3.90  tff(c_10901, plain, (![A_460]: (r1_tarski(A_460, A_460))), inference(resolution, [status(thm)], [c_10890, c_8])).
% 9.88/3.90  tff(c_10844, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 9.88/3.90  tff(c_10868, plain, (![A_450, B_451]: (r1_tarski(A_450, B_451) | ~m1_subset_1(A_450, k1_zfmisc_1(B_451)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.88/3.90  tff(c_10881, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_10868])).
% 9.88/3.90  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.88/3.90  tff(c_10913, plain, (![C_468, B_469, A_470]: (r2_hidden(C_468, B_469) | ~r2_hidden(C_468, A_470) | ~r1_tarski(A_470, B_469))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.88/3.90  tff(c_11078, plain, (![A_490, B_491, B_492]: (r2_hidden('#skF_2'(A_490, B_491), B_492) | ~r1_tarski(A_490, B_492) | r1_tarski(A_490, B_491))), inference(resolution, [status(thm)], [c_10, c_10913])).
% 9.88/3.90  tff(c_15439, plain, (![A_697, B_698, B_699, B_700]: (r2_hidden('#skF_2'(A_697, B_698), B_699) | ~r1_tarski(B_700, B_699) | ~r1_tarski(A_697, B_700) | r1_tarski(A_697, B_698))), inference(resolution, [status(thm)], [c_11078, c_6])).
% 9.88/3.90  tff(c_15551, plain, (![A_702, B_703]: (r2_hidden('#skF_2'(A_702, B_703), u1_struct_0('#skF_4')) | ~r1_tarski(A_702, '#skF_5') | r1_tarski(A_702, B_703))), inference(resolution, [status(thm)], [c_10881, c_15439])).
% 9.88/3.90  tff(c_15577, plain, (![A_702]: (~r1_tarski(A_702, '#skF_5') | r1_tarski(A_702, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_15551, c_8])).
% 9.88/3.90  tff(c_12163, plain, (![B_578, A_579]: (v1_tdlat_3(B_578) | ~v2_tex_2(u1_struct_0(B_578), A_579) | ~m1_subset_1(u1_struct_0(B_578), k1_zfmisc_1(u1_struct_0(A_579))) | ~m1_pre_topc(B_578, A_579) | v2_struct_0(B_578) | ~l1_pre_topc(A_579) | v2_struct_0(A_579))), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.88/3.90  tff(c_15663, plain, (![B_708, A_709]: (v1_tdlat_3(B_708) | ~v2_tex_2(u1_struct_0(B_708), A_709) | ~m1_pre_topc(B_708, A_709) | v2_struct_0(B_708) | ~l1_pre_topc(A_709) | v2_struct_0(A_709) | ~r1_tarski(u1_struct_0(B_708), u1_struct_0(A_709)))), inference(resolution, [status(thm)], [c_20, c_12163])).
% 9.88/3.90  tff(c_15667, plain, (![B_708]: (v1_tdlat_3(B_708) | ~v2_tex_2(u1_struct_0(B_708), '#skF_4') | ~m1_pre_topc(B_708, '#skF_4') | v2_struct_0(B_708) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(u1_struct_0(B_708), '#skF_5'))), inference(resolution, [status(thm)], [c_15577, c_15663])).
% 9.88/3.90  tff(c_15713, plain, (![B_708]: (v1_tdlat_3(B_708) | ~v2_tex_2(u1_struct_0(B_708), '#skF_4') | ~m1_pre_topc(B_708, '#skF_4') | v2_struct_0(B_708) | v2_struct_0('#skF_4') | ~r1_tarski(u1_struct_0(B_708), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_15667])).
% 9.88/3.90  tff(c_15841, plain, (![B_713]: (v1_tdlat_3(B_713) | ~v2_tex_2(u1_struct_0(B_713), '#skF_4') | ~m1_pre_topc(B_713, '#skF_4') | v2_struct_0(B_713) | ~r1_tarski(u1_struct_0(B_713), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_15713])).
% 9.88/3.90  tff(c_15862, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~r1_tarski(u1_struct_0('#skF_3'('#skF_4', '#skF_5')), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12053, c_15841])).
% 9.88/3.90  tff(c_15865, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10901, c_12053, c_11625, c_10844, c_15862])).
% 9.88/3.90  tff(c_15867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11446, c_12098, c_15865])).
% 9.88/3.90  tff(c_15868, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_12089])).
% 9.88/3.90  tff(c_15872, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_15868])).
% 9.88/3.90  tff(c_15876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11638, c_15872])).
% 9.88/3.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.88/3.90  
% 9.88/3.90  Inference rules
% 9.88/3.90  ----------------------
% 9.88/3.90  #Ref     : 0
% 9.88/3.90  #Sup     : 3530
% 9.88/3.90  #Fact    : 0
% 9.88/3.90  #Define  : 0
% 9.88/3.90  #Split   : 16
% 9.88/3.90  #Chain   : 0
% 9.88/3.90  #Close   : 0
% 9.88/3.90  
% 9.88/3.90  Ordering : KBO
% 9.88/3.90  
% 9.88/3.90  Simplification rules
% 9.88/3.90  ----------------------
% 9.88/3.90  #Subsume      : 690
% 9.88/3.90  #Demod        : 938
% 9.88/3.90  #Tautology    : 430
% 9.88/3.90  #SimpNegUnit  : 983
% 9.88/3.90  #BackRed      : 15
% 9.88/3.90  
% 9.88/3.90  #Partial instantiations: 0
% 9.88/3.90  #Strategies tried      : 1
% 9.88/3.90  
% 9.88/3.90  Timing (in seconds)
% 9.88/3.90  ----------------------
% 9.88/3.91  Preprocessing        : 0.34
% 9.88/3.91  Parsing              : 0.19
% 9.88/3.91  CNF conversion       : 0.02
% 9.88/3.91  Main loop            : 2.76
% 9.88/3.91  Inferencing          : 0.80
% 9.88/3.91  Reduction            : 0.83
% 9.88/3.91  Demodulation         : 0.51
% 9.88/3.91  BG Simplification    : 0.08
% 9.88/3.91  Subsumption          : 0.83
% 9.88/3.91  Abstraction          : 0.11
% 9.88/3.91  MUC search           : 0.00
% 9.88/3.91  Cooper               : 0.00
% 9.88/3.91  Total                : 3.17
% 9.88/3.91  Index Insertion      : 0.00
% 9.88/3.91  Index Deletion       : 0.00
% 9.88/3.91  Index Matching       : 0.00
% 9.88/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
