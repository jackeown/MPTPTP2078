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
% DateTime   : Thu Dec  3 10:29:51 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 326 expanded)
%              Number of leaves         :   43 ( 134 expanded)
%              Depth                    :   12
%              Number of atoms          :  285 (1225 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_197,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_177,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_70,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_73,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_75,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_148,plain,(
    ! [A_66,C_67,B_68] :
      ( m1_subset_1(A_66,C_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(C_67))
      | ~ r2_hidden(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_157,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_148])).

tff(c_6,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k1_tarski(A_56),k1_zfmisc_1(B_57))
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tarski(A_56),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_102,c_12])).

tff(c_224,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(A_82,B_81)
      | ~ v1_zfmisc_1(B_81)
      | v1_xboole_0(B_81)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_227,plain,(
    ! [A_56,B_57] :
      ( k1_tarski(A_56) = B_57
      | ~ v1_zfmisc_1(B_57)
      | v1_xboole_0(B_57)
      | v1_xboole_0(k1_tarski(A_56))
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_106,c_224])).

tff(c_256,plain,(
    ! [A_85,B_86] :
      ( k1_tarski(A_85) = B_86
      | ~ v1_zfmisc_1(B_86)
      | v1_xboole_0(B_86)
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_227])).

tff(c_260,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_256])).

tff(c_108,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_123,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_117])).

tff(c_158,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_148])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_161,plain,(
    ! [A_69] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_69) = k1_tarski(A_69)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_158,c_26])).

tff(c_164,plain,(
    ! [A_69] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_69) = k1_tarski(A_69)
      | ~ r2_hidden(A_69,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_161])).

tff(c_359,plain,(
    ! [A_103,B_104] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_103),B_104),A_103)
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_362,plain,(
    ! [A_69] :
      ( v2_tex_2(k1_tarski(A_69),'#skF_3')
      | ~ m1_subset_1(A_69,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_69,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_359])).

tff(c_364,plain,(
    ! [A_69] :
      ( v2_tex_2(k1_tarski(A_69),'#skF_3')
      | ~ m1_subset_1(A_69,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_69,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_362])).

tff(c_366,plain,(
    ! [A_105] :
      ( v2_tex_2(k1_tarski(A_105),'#skF_3')
      | ~ m1_subset_1(A_105,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_105,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_364])).

tff(c_382,plain,(
    ! [A_111] :
      ( v2_tex_2(A_111,'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_111),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(A_111),'#skF_4')
      | ~ v1_zfmisc_1(A_111)
      | v1_xboole_0(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_366])).

tff(c_445,plain,(
    ! [A_116] :
      ( v2_tex_2(A_116,'#skF_3')
      | ~ v1_zfmisc_1(A_116)
      | v1_xboole_0(A_116)
      | ~ r2_hidden('#skF_1'(A_116),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_157,c_382])).

tff(c_449,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_445])).

tff(c_452,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_449])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_75,c_452])).

tff(c_455,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1406,plain,(
    ! [A_239,B_240] :
      ( m1_pre_topc('#skF_2'(A_239,B_240),A_239)
      | ~ v2_tex_2(B_240,A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | v1_xboole_0(B_240)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1432,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1406])).

tff(c_1445,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_455,c_1432])).

tff(c_1446,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_1445])).

tff(c_22,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1452,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1446,c_22])).

tff(c_1459,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1452])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_889,plain,(
    ! [A_195,B_196] :
      ( ~ v2_struct_0('#skF_2'(A_195,B_196))
      | ~ v2_tex_2(B_196,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | v1_xboole_0(B_196)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_916,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_889])).

tff(c_927,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_455,c_916])).

tff(c_928,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_927])).

tff(c_58,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_36,plain,(
    ! [B_28,A_26] :
      ( v2_tdlat_3(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1449,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1446,c_36])).

tff(c_1455,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1449])).

tff(c_1456,plain,(
    v2_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1455])).

tff(c_28,plain,(
    ! [A_24] :
      ( v2_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1463,plain,
    ( v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1456,c_28])).

tff(c_1465,plain,(
    v2_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1463])).

tff(c_1245,plain,(
    ! [A_223,B_224] :
      ( v1_tdlat_3('#skF_2'(A_223,B_224))
      | ~ v2_tex_2(B_224,A_223)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | v1_xboole_0(B_224)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1280,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1245])).

tff(c_1293,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_455,c_1280])).

tff(c_1294,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_1293])).

tff(c_32,plain,(
    ! [A_25] :
      ( v7_struct_0(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_456,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1504,plain,(
    ! [A_242,B_243] :
      ( u1_struct_0('#skF_2'(A_242,B_243)) = B_243
      | ~ v2_tex_2(B_243,A_242)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | v1_xboole_0(B_243)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1543,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1504])).

tff(c_1557,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_455,c_1543])).

tff(c_1558,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_1557])).

tff(c_24,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1579,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1558,c_24])).

tff(c_1600,plain,
    ( ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_1579])).

tff(c_1602,plain,(
    ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1600])).

tff(c_1605,plain,
    ( ~ v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_1602])).

tff(c_1611,plain,(
    v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1465,c_1294,c_1456,c_1605])).

tff(c_1613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_928,c_1611])).

tff(c_1614,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1600])).

tff(c_1634,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_1614])).

tff(c_1638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.61  
% 3.81/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.61  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.81/1.61  
% 3.81/1.61  %Foreground sorts:
% 3.81/1.61  
% 3.81/1.61  
% 3.81/1.61  %Background operators:
% 3.81/1.61  
% 3.81/1.61  
% 3.81/1.61  %Foreground operators:
% 3.81/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.81/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.81/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.81/1.61  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.81/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.81/1.61  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.81/1.61  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.81/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.61  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.81/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.81/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.81/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.81/1.61  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.81/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.81/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.81/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.81/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.81/1.61  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.81/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.61  
% 3.96/1.63  tff(f_197, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.96/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.96/1.63  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.96/1.63  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.96/1.63  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.96/1.63  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.96/1.63  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.96/1.63  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.96/1.63  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.96/1.63  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 3.96/1.63  tff(f_165, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 3.96/1.63  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.96/1.63  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.96/1.63  tff(f_123, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 3.96/1.63  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 3.96/1.63  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 3.96/1.63  tff(f_78, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.96/1.63  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_70, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_73, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 3.96/1.63  tff(c_64, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_75, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_64])).
% 3.96/1.63  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.63  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_148, plain, (![A_66, C_67, B_68]: (m1_subset_1(A_66, C_67) | ~m1_subset_1(B_68, k1_zfmisc_1(C_67)) | ~r2_hidden(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.96/1.63  tff(c_157, plain, (![A_66]: (m1_subset_1(A_66, u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_148])).
% 3.96/1.63  tff(c_6, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.96/1.63  tff(c_102, plain, (![A_56, B_57]: (m1_subset_1(k1_tarski(A_56), k1_zfmisc_1(B_57)) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.96/1.63  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.96/1.63  tff(c_106, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), B_57) | ~r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_102, c_12])).
% 3.96/1.63  tff(c_224, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(A_82, B_81) | ~v1_zfmisc_1(B_81) | v1_xboole_0(B_81) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.96/1.63  tff(c_227, plain, (![A_56, B_57]: (k1_tarski(A_56)=B_57 | ~v1_zfmisc_1(B_57) | v1_xboole_0(B_57) | v1_xboole_0(k1_tarski(A_56)) | ~r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_106, c_224])).
% 3.96/1.63  tff(c_256, plain, (![A_85, B_86]: (k1_tarski(A_85)=B_86 | ~v1_zfmisc_1(B_86) | v1_xboole_0(B_86) | ~r2_hidden(A_85, B_86))), inference(negUnitSimplification, [status(thm)], [c_6, c_227])).
% 3.96/1.63  tff(c_260, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_256])).
% 3.96/1.63  tff(c_108, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.96/1.63  tff(c_117, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_108])).
% 3.96/1.63  tff(c_123, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_117])).
% 3.96/1.63  tff(c_158, plain, (![A_69]: (m1_subset_1(A_69, u1_struct_0('#skF_3')) | ~r2_hidden(A_69, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_148])).
% 3.96/1.63  tff(c_26, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.96/1.63  tff(c_161, plain, (![A_69]: (k6_domain_1(u1_struct_0('#skF_3'), A_69)=k1_tarski(A_69) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_69, '#skF_4'))), inference(resolution, [status(thm)], [c_158, c_26])).
% 3.96/1.63  tff(c_164, plain, (![A_69]: (k6_domain_1(u1_struct_0('#skF_3'), A_69)=k1_tarski(A_69) | ~r2_hidden(A_69, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_123, c_161])).
% 3.96/1.63  tff(c_359, plain, (![A_103, B_104]: (v2_tex_2(k6_domain_1(u1_struct_0(A_103), B_104), A_103) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.96/1.63  tff(c_362, plain, (![A_69]: (v2_tex_2(k1_tarski(A_69), '#skF_3') | ~m1_subset_1(A_69, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_69, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_359])).
% 3.96/1.63  tff(c_364, plain, (![A_69]: (v2_tex_2(k1_tarski(A_69), '#skF_3') | ~m1_subset_1(A_69, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(A_69, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_362])).
% 3.96/1.63  tff(c_366, plain, (![A_105]: (v2_tex_2(k1_tarski(A_105), '#skF_3') | ~m1_subset_1(A_105, u1_struct_0('#skF_3')) | ~r2_hidden(A_105, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_364])).
% 3.96/1.63  tff(c_382, plain, (![A_111]: (v2_tex_2(A_111, '#skF_3') | ~m1_subset_1('#skF_1'(A_111), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'(A_111), '#skF_4') | ~v1_zfmisc_1(A_111) | v1_xboole_0(A_111))), inference(superposition, [status(thm), theory('equality')], [c_260, c_366])).
% 3.96/1.63  tff(c_445, plain, (![A_116]: (v2_tex_2(A_116, '#skF_3') | ~v1_zfmisc_1(A_116) | v1_xboole_0(A_116) | ~r2_hidden('#skF_1'(A_116), '#skF_4'))), inference(resolution, [status(thm)], [c_157, c_382])).
% 3.96/1.63  tff(c_449, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_445])).
% 3.96/1.63  tff(c_452, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_449])).
% 3.96/1.63  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_75, c_452])).
% 3.96/1.63  tff(c_455, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 3.96/1.63  tff(c_1406, plain, (![A_239, B_240]: (m1_pre_topc('#skF_2'(A_239, B_240), A_239) | ~v2_tex_2(B_240, A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | v1_xboole_0(B_240) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.96/1.63  tff(c_1432, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1406])).
% 3.96/1.63  tff(c_1445, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_455, c_1432])).
% 3.96/1.63  tff(c_1446, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_1445])).
% 3.96/1.63  tff(c_22, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.96/1.63  tff(c_1452, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1446, c_22])).
% 3.96/1.63  tff(c_1459, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1452])).
% 3.96/1.63  tff(c_20, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.96/1.63  tff(c_889, plain, (![A_195, B_196]: (~v2_struct_0('#skF_2'(A_195, B_196)) | ~v2_tex_2(B_196, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | v1_xboole_0(B_196) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.96/1.63  tff(c_916, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_889])).
% 3.96/1.63  tff(c_927, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_455, c_916])).
% 3.96/1.63  tff(c_928, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_927])).
% 3.96/1.63  tff(c_58, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.96/1.63  tff(c_36, plain, (![B_28, A_26]: (v2_tdlat_3(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.96/1.63  tff(c_1449, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1446, c_36])).
% 3.96/1.63  tff(c_1455, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1449])).
% 3.96/1.63  tff(c_1456, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_1455])).
% 3.96/1.63  tff(c_28, plain, (![A_24]: (v2_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.96/1.63  tff(c_1463, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_1456, c_28])).
% 3.96/1.63  tff(c_1465, plain, (v2_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1463])).
% 3.96/1.63  tff(c_1245, plain, (![A_223, B_224]: (v1_tdlat_3('#skF_2'(A_223, B_224)) | ~v2_tex_2(B_224, A_223) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | v1_xboole_0(B_224) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.96/1.63  tff(c_1280, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1245])).
% 3.96/1.63  tff(c_1293, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_455, c_1280])).
% 3.96/1.63  tff(c_1294, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_1293])).
% 3.96/1.63  tff(c_32, plain, (![A_25]: (v7_struct_0(A_25) | ~v2_tdlat_3(A_25) | ~v1_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.96/1.63  tff(c_456, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 3.96/1.63  tff(c_1504, plain, (![A_242, B_243]: (u1_struct_0('#skF_2'(A_242, B_243))=B_243 | ~v2_tex_2(B_243, A_242) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | v1_xboole_0(B_243) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.96/1.63  tff(c_1543, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1504])).
% 3.96/1.63  tff(c_1557, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_455, c_1543])).
% 3.96/1.63  tff(c_1558, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_1557])).
% 3.96/1.63  tff(c_24, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.96/1.63  tff(c_1579, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1558, c_24])).
% 3.96/1.63  tff(c_1600, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_456, c_1579])).
% 3.96/1.63  tff(c_1602, plain, (~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1600])).
% 3.96/1.63  tff(c_1605, plain, (~v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_1602])).
% 3.96/1.63  tff(c_1611, plain, (v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1465, c_1294, c_1456, c_1605])).
% 3.96/1.63  tff(c_1613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_928, c_1611])).
% 3.96/1.63  tff(c_1614, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1600])).
% 3.96/1.63  tff(c_1634, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_1614])).
% 3.96/1.63  tff(c_1638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1634])).
% 3.96/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.63  
% 3.96/1.63  Inference rules
% 3.96/1.63  ----------------------
% 3.96/1.63  #Ref     : 0
% 3.96/1.63  #Sup     : 312
% 3.96/1.63  #Fact    : 0
% 3.96/1.63  #Define  : 0
% 3.96/1.63  #Split   : 8
% 3.96/1.63  #Chain   : 0
% 3.96/1.63  #Close   : 0
% 3.96/1.63  
% 3.96/1.63  Ordering : KBO
% 3.96/1.63  
% 3.96/1.63  Simplification rules
% 3.96/1.63  ----------------------
% 3.96/1.63  #Subsume      : 39
% 3.96/1.63  #Demod        : 56
% 3.96/1.63  #Tautology    : 68
% 3.96/1.63  #SimpNegUnit  : 64
% 3.96/1.63  #BackRed      : 0
% 3.96/1.63  
% 3.96/1.63  #Partial instantiations: 0
% 3.96/1.63  #Strategies tried      : 1
% 3.96/1.63  
% 3.96/1.63  Timing (in seconds)
% 3.96/1.63  ----------------------
% 3.96/1.63  Preprocessing        : 0.34
% 3.96/1.63  Parsing              : 0.19
% 3.96/1.63  CNF conversion       : 0.02
% 3.96/1.63  Main loop            : 0.52
% 3.96/1.64  Inferencing          : 0.20
% 3.96/1.64  Reduction            : 0.14
% 3.96/1.64  Demodulation         : 0.08
% 3.96/1.64  BG Simplification    : 0.03
% 3.96/1.64  Subsumption          : 0.10
% 3.96/1.64  Abstraction          : 0.03
% 3.96/1.64  MUC search           : 0.00
% 3.96/1.64  Cooper               : 0.00
% 3.96/1.64  Total                : 0.90
% 3.96/1.64  Index Insertion      : 0.00
% 3.96/1.64  Index Deletion       : 0.00
% 3.96/1.64  Index Matching       : 0.00
% 3.96/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
