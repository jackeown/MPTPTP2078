%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:33 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 148 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 409 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > o_2_0_compts_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(o_2_0_compts_1,type,(
    o_2_0_compts_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(o_2_0_compts_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_0_compts_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_63,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [B_36,A_37] :
      ( ~ r1_tarski(B_36,A_37)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(A_37,B_36) ) ),
    inference(resolution,[status(thm)],[c_63,c_12])).

tff(c_72,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_39,c_68])).

tff(c_73,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_91,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(o_2_0_compts_1(A_47,B_48),B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [A_47] :
      ( m1_subset_1(o_2_0_compts_1(A_47,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_102,plain,(
    ! [A_49] :
      ( ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_97])).

tff(c_105,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_105])).

tff(c_110,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_148,plain,(
    ! [B_66,A_67] :
      ( v2_tex_2(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v1_xboole_0(B_66)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_156,plain,(
    ! [A_67] :
      ( v2_tex_2(k1_xboole_0,A_67)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_2,c_148])).

tff(c_160,plain,(
    ! [A_67] :
      ( v2_tex_2(k1_xboole_0,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_156])).

tff(c_197,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1('#skF_1'(A_80,B_81),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v3_tdlat_3(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [B_23] :
      ( ~ v3_tex_2(B_23,'#skF_2')
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_212,plain,(
    ! [B_81] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_81),'#skF_2')
      | ~ v2_tex_2(B_81,'#skF_2')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_197,c_24])).

tff(c_223,plain,(
    ! [B_81] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_81),'#skF_2')
      | ~ v2_tex_2(B_81,'#skF_2')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_212])).

tff(c_226,plain,(
    ! [B_82] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_82),'#skF_2')
      | ~ v2_tex_2(B_82,'#skF_2')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_223])).

tff(c_244,plain,
    ( ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2')
    | ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_226])).

tff(c_253,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_256,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_253])).

tff(c_259,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_256])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_259])).

tff(c_263,plain,(
    v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    ! [A_71,B_72] :
      ( v3_tex_2('#skF_1'(A_71,B_72),A_71)
      | ~ v2_tex_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v3_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_177,plain,(
    ! [A_71,A_4] :
      ( v3_tex_2('#skF_1'(A_71,A_4),A_71)
      | ~ v2_tex_2(A_4,A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v3_tdlat_3(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71)
      | ~ r1_tarski(A_4,u1_struct_0(A_71)) ) ),
    inference(resolution,[status(thm)],[c_8,c_170])).

tff(c_262,plain,(
    ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_266,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_177,c_262])).

tff(c_272,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_30,c_28,c_26,c_263,c_266])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.25  
% 2.26/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.25  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > o_2_0_compts_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.26/1.25  
% 2.26/1.25  %Foreground sorts:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Background operators:
% 2.26/1.25  
% 2.26/1.25  
% 2.26/1.25  %Foreground operators:
% 2.26/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.25  tff(o_2_0_compts_1, type, o_2_0_compts_1: ($i * $i) > $i).
% 2.26/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.26/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.25  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.26/1.25  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.26/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.25  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.26/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.25  
% 2.26/1.27  tff(f_108, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.26/1.27  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.26/1.27  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.26/1.27  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.26/1.27  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.26/1.27  tff(f_56, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(o_2_0_compts_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_0_compts_1)).
% 2.26/1.27  tff(f_70, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.26/1.27  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.26/1.27  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.26/1.27  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.26/1.27  tff(c_35, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.27  tff(c_39, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_35])).
% 2.26/1.27  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.26/1.27  tff(c_28, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.26/1.27  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.26/1.27  tff(c_63, plain, (![A_34, B_35]: (r2_hidden(A_34, B_35) | v1_xboole_0(B_35) | ~m1_subset_1(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.27  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.27  tff(c_68, plain, (![B_36, A_37]: (~r1_tarski(B_36, A_37) | v1_xboole_0(B_36) | ~m1_subset_1(A_37, B_36))), inference(resolution, [status(thm)], [c_63, c_12])).
% 2.26/1.27  tff(c_72, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_39, c_68])).
% 2.26/1.27  tff(c_73, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_72])).
% 2.26/1.27  tff(c_91, plain, (![A_47, B_48]: (m1_subset_1(o_2_0_compts_1(A_47, B_48), B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.27  tff(c_97, plain, (![A_47]: (m1_subset_1(o_2_0_compts_1(A_47, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(resolution, [status(thm)], [c_2, c_91])).
% 2.26/1.27  tff(c_102, plain, (![A_49]: (~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(negUnitSimplification, [status(thm)], [c_73, c_97])).
% 2.26/1.27  tff(c_105, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_102])).
% 2.26/1.27  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_105])).
% 2.26/1.27  tff(c_110, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_72])).
% 2.26/1.27  tff(c_148, plain, (![B_66, A_67]: (v2_tex_2(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~v1_xboole_0(B_66) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.27  tff(c_156, plain, (![A_67]: (v2_tex_2(k1_xboole_0, A_67) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_2, c_148])).
% 2.26/1.27  tff(c_160, plain, (![A_67]: (v2_tex_2(k1_xboole_0, A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_156])).
% 2.26/1.27  tff(c_197, plain, (![A_80, B_81]: (m1_subset_1('#skF_1'(A_80, B_81), k1_zfmisc_1(u1_struct_0(A_80))) | ~v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v3_tdlat_3(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.26/1.27  tff(c_24, plain, (![B_23]: (~v3_tex_2(B_23, '#skF_2') | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.26/1.27  tff(c_212, plain, (![B_81]: (~v3_tex_2('#skF_1'('#skF_2', B_81), '#skF_2') | ~v2_tex_2(B_81, '#skF_2') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_197, c_24])).
% 2.26/1.27  tff(c_223, plain, (![B_81]: (~v3_tex_2('#skF_1'('#skF_2', B_81), '#skF_2') | ~v2_tex_2(B_81, '#skF_2') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_212])).
% 2.26/1.27  tff(c_226, plain, (![B_82]: (~v3_tex_2('#skF_1'('#skF_2', B_82), '#skF_2') | ~v2_tex_2(B_82, '#skF_2') | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_223])).
% 2.26/1.27  tff(c_244, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2') | ~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_2, c_226])).
% 2.26/1.27  tff(c_253, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_244])).
% 2.26/1.27  tff(c_256, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_160, c_253])).
% 2.26/1.27  tff(c_259, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_256])).
% 2.26/1.27  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_259])).
% 2.26/1.27  tff(c_263, plain, (v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_244])).
% 2.26/1.27  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.27  tff(c_170, plain, (![A_71, B_72]: (v3_tex_2('#skF_1'(A_71, B_72), A_71) | ~v2_tex_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v3_tdlat_3(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.26/1.27  tff(c_177, plain, (![A_71, A_4]: (v3_tex_2('#skF_1'(A_71, A_4), A_71) | ~v2_tex_2(A_4, A_71) | ~l1_pre_topc(A_71) | ~v3_tdlat_3(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71) | ~r1_tarski(A_4, u1_struct_0(A_71)))), inference(resolution, [status(thm)], [c_8, c_170])).
% 2.26/1.27  tff(c_262, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2')), inference(splitRight, [status(thm)], [c_244])).
% 2.26/1.27  tff(c_266, plain, (~v2_tex_2(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_177, c_262])).
% 2.26/1.27  tff(c_272, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_30, c_28, c_26, c_263, c_266])).
% 2.26/1.27  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_272])).
% 2.26/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.27  
% 2.26/1.27  Inference rules
% 2.26/1.27  ----------------------
% 2.26/1.27  #Ref     : 0
% 2.26/1.27  #Sup     : 44
% 2.26/1.27  #Fact    : 0
% 2.26/1.27  #Define  : 0
% 2.26/1.27  #Split   : 2
% 2.26/1.27  #Chain   : 0
% 2.26/1.27  #Close   : 0
% 2.26/1.27  
% 2.26/1.27  Ordering : KBO
% 2.26/1.27  
% 2.26/1.27  Simplification rules
% 2.26/1.27  ----------------------
% 2.26/1.27  #Subsume      : 5
% 2.26/1.27  #Demod        : 23
% 2.26/1.27  #Tautology    : 5
% 2.26/1.27  #SimpNegUnit  : 6
% 2.26/1.27  #BackRed      : 0
% 2.26/1.27  
% 2.26/1.27  #Partial instantiations: 0
% 2.26/1.27  #Strategies tried      : 1
% 2.26/1.27  
% 2.26/1.27  Timing (in seconds)
% 2.26/1.27  ----------------------
% 2.26/1.27  Preprocessing        : 0.28
% 2.26/1.27  Parsing              : 0.16
% 2.26/1.27  CNF conversion       : 0.02
% 2.26/1.27  Main loop            : 0.21
% 2.26/1.27  Inferencing          : 0.09
% 2.26/1.27  Reduction            : 0.05
% 2.26/1.27  Demodulation         : 0.03
% 2.26/1.27  BG Simplification    : 0.01
% 2.26/1.27  Subsumption          : 0.04
% 2.26/1.27  Abstraction          : 0.01
% 2.26/1.27  MUC search           : 0.00
% 2.26/1.27  Cooper               : 0.00
% 2.26/1.27  Total                : 0.53
% 2.26/1.27  Index Insertion      : 0.00
% 2.26/1.27  Index Deletion       : 0.00
% 2.26/1.27  Index Matching       : 0.00
% 2.26/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
