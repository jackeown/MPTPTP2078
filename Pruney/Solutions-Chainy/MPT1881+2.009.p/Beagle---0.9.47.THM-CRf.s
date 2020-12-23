%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:07 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 430 expanded)
%              Number of leaves         :   33 ( 158 expanded)
%              Depth                    :   17
%              Number of atoms          :  223 (1094 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_48,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_45,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_85,axiom,(
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

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_11] : ~ v1_subset_1(k2_subset_1(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [A_11] : ~ v1_subset_1(A_11,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_22,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_492,plain,(
    ! [B_112,A_113] :
      ( v2_tex_2(B_112,A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v1_tdlat_3(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_504,plain,(
    ! [A_113] :
      ( v2_tex_2(u1_struct_0(A_113),A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v1_tdlat_3(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_68,c_492])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_85,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_86,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_66])).

tff(c_121,plain,(
    ! [B_47,A_48] :
      ( v1_subset_1(B_47,A_48)
      | B_47 = A_48
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_121])).

tff(c_130,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_124])).

tff(c_24,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_99,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_43,A_3] :
      ( r1_tarski(A_43,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_107,plain,(
    ! [A_45,A_46] :
      ( r1_tarski(A_45,A_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_46)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_103])).

tff(c_114,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_120,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_135,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_120])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_142,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_211,plain,(
    ! [B_65,A_66] :
      ( v2_tex_2(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v1_tdlat_3(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_214,plain,(
    ! [B_65] :
      ( v2_tex_2(B_65,'#skF_4')
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_211])).

tff(c_220,plain,(
    ! [B_65] :
      ( v2_tex_2(B_65,'#skF_4')
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_214])).

tff(c_223,plain,(
    ! [B_67] :
      ( v2_tex_2(B_67,'#skF_4')
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_220])).

tff(c_228,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_223])).

tff(c_343,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_3'(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | v3_tex_2(B_86,A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_365,plain,(
    ! [B_86] :
      ( m1_subset_1('#skF_3'('#skF_4',B_86),k1_zfmisc_1('#skF_5'))
      | v3_tex_2(B_86,'#skF_4')
      | ~ v2_tex_2(B_86,'#skF_4')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_343])).

tff(c_375,plain,(
    ! [B_87] :
      ( m1_subset_1('#skF_3'('#skF_4',B_87),k1_zfmisc_1('#skF_5'))
      | v3_tex_2(B_87,'#skF_4')
      | ~ v2_tex_2(B_87,'#skF_4')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142,c_365])).

tff(c_106,plain,(
    ! [A_43,A_3] :
      ( r1_tarski(A_43,A_3)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_103])).

tff(c_392,plain,(
    ! [B_88] :
      ( r1_tarski('#skF_3'('#skF_4',B_88),'#skF_5')
      | v3_tex_2(B_88,'#skF_4')
      | ~ v2_tex_2(B_88,'#skF_4')
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_375,c_106])).

tff(c_236,plain,(
    ! [A_69,B_70] :
      ( '#skF_3'(A_69,B_70) != B_70
      | v3_tex_2(B_70,A_69)
      | ~ v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_239,plain,(
    ! [B_70] :
      ( '#skF_3'('#skF_4',B_70) != B_70
      | v3_tex_2(B_70,'#skF_4')
      | ~ v2_tex_2(B_70,'#skF_4')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_236])).

tff(c_247,plain,(
    ! [B_71] :
      ( '#skF_3'('#skF_4',B_71) != B_71
      | v3_tex_2(B_71,'#skF_4')
      | ~ v2_tex_2(B_71,'#skF_4')
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_239])).

tff(c_251,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_247])).

tff(c_254,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_251])).

tff(c_255,plain,(
    '#skF_3'('#skF_4','#skF_5') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_254])).

tff(c_308,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,'#skF_3'(A_82,B_81))
      | v3_tex_2(B_81,A_82)
      | ~ v2_tex_2(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_321,plain,(
    ! [A_84] :
      ( r1_tarski(u1_struct_0(A_84),'#skF_3'(A_84,u1_struct_0(A_84)))
      | v3_tex_2(u1_struct_0(A_84),A_84)
      | ~ v2_tex_2(u1_struct_0(A_84),A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_68,c_308])).

tff(c_326,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4',u1_struct_0('#skF_4')))
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_321])).

tff(c_332,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_228,c_142,c_142,c_142,c_326])).

tff(c_333,plain,(
    r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_332])).

tff(c_338,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_333,c_2])).

tff(c_341,plain,(
    ~ r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_338])).

tff(c_395,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_392,c_341])).

tff(c_400,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_228,c_395])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_400])).

tff(c_404,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_418,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(A_93,B_94)
      | v1_xboole_0(B_94)
      | ~ m1_subset_1(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_422,plain,(
    ! [A_93,A_3] :
      ( r1_tarski(A_93,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_93,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_418,c_8])).

tff(c_426,plain,(
    ! [A_95,A_96] :
      ( r1_tarski(A_95,A_96)
      | ~ m1_subset_1(A_95,k1_zfmisc_1(A_96)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_422])).

tff(c_433,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_426])).

tff(c_641,plain,(
    ! [C_144,B_145,A_146] :
      ( C_144 = B_145
      | ~ r1_tarski(B_145,C_144)
      | ~ v2_tex_2(C_144,A_146)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ v3_tex_2(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_664,plain,(
    ! [A_146] :
      ( u1_struct_0('#skF_4') = '#skF_5'
      | ~ v2_tex_2(u1_struct_0('#skF_4'),A_146)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ v3_tex_2('#skF_5',A_146)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(resolution,[status(thm)],[c_433,c_641])).

tff(c_686,plain,(
    ! [A_151] :
      ( ~ v2_tex_2(u1_struct_0('#skF_4'),A_151)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ v3_tex_2('#skF_5',A_151)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_690,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_686])).

tff(c_693,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_404,c_690])).

tff(c_696,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_504,c_693])).

tff(c_699,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_696])).

tff(c_701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_699])).

tff(c_702,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_451,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_433,c_2])).

tff(c_452,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_451])).

tff(c_703,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_452])).

tff(c_709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_703])).

tff(c_710,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_451])).

tff(c_403,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_713,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_403])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 18:57:21 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.58  
% 3.11/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.59  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.11/1.59  
% 3.11/1.59  %Foreground sorts:
% 3.11/1.59  
% 3.11/1.59  
% 3.11/1.59  %Background operators:
% 3.11/1.59  
% 3.11/1.59  
% 3.11/1.59  %Foreground operators:
% 3.11/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.59  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.11/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.59  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.11/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.11/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.59  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.11/1.59  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.11/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.11/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.11/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.59  
% 3.11/1.61  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.11/1.61  tff(f_48, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.11/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.11/1.61  tff(f_117, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.11/1.61  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.11/1.61  tff(f_99, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.11/1.61  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.11/1.61  tff(f_45, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.11/1.61  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.11/1.61  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.11/1.61  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.11/1.61  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.11/1.61  tff(c_26, plain, (![A_11]: (~v1_subset_1(k2_subset_1(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.61  tff(c_67, plain, (![A_11]: (~v1_subset_1(A_11, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 3.11/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.61  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.61  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.61  tff(c_54, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.61  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.61  tff(c_22, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.11/1.61  tff(c_68, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 3.11/1.61  tff(c_492, plain, (![B_112, A_113]: (v2_tex_2(B_112, A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v1_tdlat_3(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.61  tff(c_504, plain, (![A_113]: (v2_tex_2(u1_struct_0(A_113), A_113) | ~l1_pre_topc(A_113) | ~v1_tdlat_3(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_68, c_492])).
% 3.11/1.61  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.61  tff(c_60, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.61  tff(c_85, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 3.11/1.61  tff(c_66, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.61  tff(c_86, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_85, c_66])).
% 3.11/1.61  tff(c_121, plain, (![B_47, A_48]: (v1_subset_1(B_47, A_48) | B_47=A_48 | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.11/1.61  tff(c_124, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_50, c_121])).
% 3.11/1.61  tff(c_130, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_86, c_124])).
% 3.11/1.61  tff(c_24, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.11/1.61  tff(c_99, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.11/1.61  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.11/1.61  tff(c_103, plain, (![A_43, A_3]: (r1_tarski(A_43, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_43, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_99, c_8])).
% 3.11/1.61  tff(c_107, plain, (![A_45, A_46]: (r1_tarski(A_45, A_46) | ~m1_subset_1(A_45, k1_zfmisc_1(A_46)))), inference(negUnitSimplification, [status(thm)], [c_24, c_103])).
% 3.11/1.61  tff(c_114, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_107])).
% 3.11/1.61  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.61  tff(c_119, plain, (u1_struct_0('#skF_4')='#skF_5' | ~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_114, c_2])).
% 3.11/1.61  tff(c_120, plain, (~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_119])).
% 3.11/1.61  tff(c_135, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_120])).
% 3.11/1.61  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_135])).
% 3.11/1.61  tff(c_142, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_119])).
% 3.11/1.61  tff(c_211, plain, (![B_65, A_66]: (v2_tex_2(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v1_tdlat_3(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.61  tff(c_214, plain, (![B_65]: (v2_tex_2(B_65, '#skF_4') | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_211])).
% 3.11/1.61  tff(c_220, plain, (![B_65]: (v2_tex_2(B_65, '#skF_4') | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_214])).
% 3.11/1.61  tff(c_223, plain, (![B_67]: (v2_tex_2(B_67, '#skF_4') | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_220])).
% 3.11/1.61  tff(c_228, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_223])).
% 3.11/1.61  tff(c_343, plain, (![A_85, B_86]: (m1_subset_1('#skF_3'(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | v3_tex_2(B_86, A_85) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.11/1.61  tff(c_365, plain, (![B_86]: (m1_subset_1('#skF_3'('#skF_4', B_86), k1_zfmisc_1('#skF_5')) | v3_tex_2(B_86, '#skF_4') | ~v2_tex_2(B_86, '#skF_4') | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_343])).
% 3.11/1.61  tff(c_375, plain, (![B_87]: (m1_subset_1('#skF_3'('#skF_4', B_87), k1_zfmisc_1('#skF_5')) | v3_tex_2(B_87, '#skF_4') | ~v2_tex_2(B_87, '#skF_4') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142, c_365])).
% 3.11/1.61  tff(c_106, plain, (![A_43, A_3]: (r1_tarski(A_43, A_3) | ~m1_subset_1(A_43, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_24, c_103])).
% 3.11/1.61  tff(c_392, plain, (![B_88]: (r1_tarski('#skF_3'('#skF_4', B_88), '#skF_5') | v3_tex_2(B_88, '#skF_4') | ~v2_tex_2(B_88, '#skF_4') | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_375, c_106])).
% 3.11/1.61  tff(c_236, plain, (![A_69, B_70]: ('#skF_3'(A_69, B_70)!=B_70 | v3_tex_2(B_70, A_69) | ~v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.11/1.61  tff(c_239, plain, (![B_70]: ('#skF_3'('#skF_4', B_70)!=B_70 | v3_tex_2(B_70, '#skF_4') | ~v2_tex_2(B_70, '#skF_4') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_236])).
% 3.11/1.61  tff(c_247, plain, (![B_71]: ('#skF_3'('#skF_4', B_71)!=B_71 | v3_tex_2(B_71, '#skF_4') | ~v2_tex_2(B_71, '#skF_4') | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_239])).
% 3.11/1.61  tff(c_251, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_247])).
% 3.11/1.61  tff(c_254, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_251])).
% 3.11/1.61  tff(c_255, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_85, c_254])).
% 3.11/1.61  tff(c_308, plain, (![B_81, A_82]: (r1_tarski(B_81, '#skF_3'(A_82, B_81)) | v3_tex_2(B_81, A_82) | ~v2_tex_2(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.11/1.61  tff(c_321, plain, (![A_84]: (r1_tarski(u1_struct_0(A_84), '#skF_3'(A_84, u1_struct_0(A_84))) | v3_tex_2(u1_struct_0(A_84), A_84) | ~v2_tex_2(u1_struct_0(A_84), A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_68, c_308])).
% 3.11/1.61  tff(c_326, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', u1_struct_0('#skF_4'))) | v3_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_142, c_321])).
% 3.11/1.61  tff(c_332, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_228, c_142, c_142, c_142, c_326])).
% 3.11/1.61  tff(c_333, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_85, c_332])).
% 3.11/1.61  tff(c_338, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_333, c_2])).
% 3.11/1.61  tff(c_341, plain, (~r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_255, c_338])).
% 3.11/1.61  tff(c_395, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_392, c_341])).
% 3.11/1.61  tff(c_400, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_228, c_395])).
% 3.11/1.61  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_400])).
% 3.11/1.61  tff(c_404, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.11/1.61  tff(c_418, plain, (![A_93, B_94]: (r2_hidden(A_93, B_94) | v1_xboole_0(B_94) | ~m1_subset_1(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.11/1.61  tff(c_422, plain, (![A_93, A_3]: (r1_tarski(A_93, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_93, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_418, c_8])).
% 3.11/1.61  tff(c_426, plain, (![A_95, A_96]: (r1_tarski(A_95, A_96) | ~m1_subset_1(A_95, k1_zfmisc_1(A_96)))), inference(negUnitSimplification, [status(thm)], [c_24, c_422])).
% 3.11/1.61  tff(c_433, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_426])).
% 3.11/1.61  tff(c_641, plain, (![C_144, B_145, A_146]: (C_144=B_145 | ~r1_tarski(B_145, C_144) | ~v2_tex_2(C_144, A_146) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_146))) | ~v3_tex_2(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.11/1.61  tff(c_664, plain, (![A_146]: (u1_struct_0('#skF_4')='#skF_5' | ~v2_tex_2(u1_struct_0('#skF_4'), A_146) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_146))) | ~v3_tex_2('#skF_5', A_146) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(resolution, [status(thm)], [c_433, c_641])).
% 3.11/1.61  tff(c_686, plain, (![A_151]: (~v2_tex_2(u1_struct_0('#skF_4'), A_151) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_151))) | ~v3_tex_2('#skF_5', A_151) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(splitLeft, [status(thm)], [c_664])).
% 3.11/1.61  tff(c_690, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_686])).
% 3.11/1.61  tff(c_693, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_404, c_690])).
% 3.11/1.61  tff(c_696, plain, (~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_504, c_693])).
% 3.11/1.61  tff(c_699, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_696])).
% 3.11/1.61  tff(c_701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_699])).
% 3.11/1.61  tff(c_702, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_664])).
% 3.11/1.61  tff(c_451, plain, (u1_struct_0('#skF_4')='#skF_5' | ~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_433, c_2])).
% 3.11/1.61  tff(c_452, plain, (~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_451])).
% 3.11/1.61  tff(c_703, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_452])).
% 3.11/1.61  tff(c_709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_703])).
% 3.11/1.61  tff(c_710, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_451])).
% 3.11/1.61  tff(c_403, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 3.11/1.61  tff(c_713, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_710, c_403])).
% 3.11/1.61  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_713])).
% 3.11/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.61  
% 3.11/1.61  Inference rules
% 3.11/1.61  ----------------------
% 3.11/1.61  #Ref     : 0
% 3.11/1.61  #Sup     : 116
% 3.11/1.61  #Fact    : 0
% 3.11/1.61  #Define  : 0
% 3.11/1.61  #Split   : 4
% 3.11/1.61  #Chain   : 0
% 3.11/1.61  #Close   : 0
% 3.11/1.61  
% 3.11/1.61  Ordering : KBO
% 3.11/1.61  
% 3.11/1.61  Simplification rules
% 3.11/1.61  ----------------------
% 3.11/1.61  #Subsume      : 14
% 3.11/1.61  #Demod        : 90
% 3.11/1.61  #Tautology    : 39
% 3.11/1.61  #SimpNegUnit  : 23
% 3.11/1.61  #BackRed      : 14
% 3.11/1.61  
% 3.11/1.61  #Partial instantiations: 0
% 3.11/1.61  #Strategies tried      : 1
% 3.11/1.61  
% 3.11/1.61  Timing (in seconds)
% 3.11/1.61  ----------------------
% 3.11/1.61  Preprocessing        : 0.33
% 3.11/1.61  Parsing              : 0.18
% 3.11/1.61  CNF conversion       : 0.02
% 3.11/1.61  Main loop            : 0.41
% 3.11/1.61  Inferencing          : 0.16
% 3.11/1.61  Reduction            : 0.11
% 3.11/1.61  Demodulation         : 0.08
% 3.11/1.61  BG Simplification    : 0.02
% 3.11/1.61  Subsumption          : 0.09
% 3.11/1.61  Abstraction          : 0.02
% 3.11/1.61  MUC search           : 0.00
% 3.11/1.61  Cooper               : 0.00
% 3.11/1.61  Total                : 0.78
% 3.11/1.61  Index Insertion      : 0.00
% 3.11/1.61  Index Deletion       : 0.00
% 3.11/1.61  Index Matching       : 0.00
% 3.11/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
