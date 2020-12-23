%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:33 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 139 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 400 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > o_2_1_compts_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(o_2_1_compts_1,type,(
    o_2_1_compts_1: ( $i * $i ) > $i )).

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

tff(f_109,negated_conjecture,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(o_2_1_compts_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_1_compts_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_94,axiom,(
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

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r2_hidden(A_27,B_28)
      | v1_xboole_0(B_28)
      | ~ m1_subset_1(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    ! [B_30,A_31] :
      ( ~ r1_tarski(B_30,A_31)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_31,B_30) ) ),
    inference(resolution,[status(thm)],[c_34,c_10])).

tff(c_49,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_50,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(o_2_1_compts_1(A_38,B_39),B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_38] :
      ( m1_subset_1(o_2_1_compts_1(A_38,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_68,plain,(
    ! [A_40] :
      ( ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_64])).

tff(c_71,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_30])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_71])).

tff(c_76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_93,plain,(
    ! [B_49,A_50] :
      ( v2_tex_2(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v1_xboole_0(B_49)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ! [A_50] :
      ( v2_tex_2(k1_xboole_0,A_50)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_100,plain,(
    ! [A_50] :
      ( v2_tex_2(k1_xboole_0,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_97])).

tff(c_114,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1('#skF_1'(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ v2_tex_2(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v3_tdlat_3(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [B_22] :
      ( ~ v3_tex_2(B_22,'#skF_2')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_129,plain,(
    ! [B_58] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_58),'#skF_2')
      | ~ v2_tex_2(B_58,'#skF_2')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_114,c_22])).

tff(c_137,plain,(
    ! [B_58] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_58),'#skF_2')
      | ~ v2_tex_2(B_58,'#skF_2')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_129])).

tff(c_139,plain,(
    ! [B_59] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_59),'#skF_2')
      | ~ v2_tex_2(B_59,'#skF_2')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_137])).

tff(c_152,plain,
    ( ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2')
    | ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_139])).

tff(c_154,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_157,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_154])).

tff(c_160,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_157])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_160])).

tff(c_164,plain,(
    v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_102,plain,(
    ! [A_52,B_53] :
      ( v3_tex_2('#skF_1'(A_52,B_53),A_52)
      | ~ v2_tex_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v3_tdlat_3(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_106,plain,(
    ! [A_52] :
      ( v3_tex_2('#skF_1'(A_52,k1_xboole_0),A_52)
      | ~ v2_tex_2(k1_xboole_0,A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v3_tdlat_3(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_163,plain,(
    ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_167,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_163])).

tff(c_170,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_164,c_167])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:19:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.26  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > o_2_1_compts_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.19/1.26  
% 2.19/1.26  %Foreground sorts:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Background operators:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Foreground operators:
% 2.19/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.19/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.26  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.19/1.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.19/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.26  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.26  tff(o_2_1_compts_1, type, o_2_1_compts_1: ($i * $i) > $i).
% 2.19/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.19/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.26  
% 2.19/1.28  tff(f_109, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.19/1.28  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.19/1.28  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.19/1.28  tff(f_46, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.19/1.28  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.19/1.28  tff(f_57, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(o_2_1_compts_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_1_compts_1)).
% 2.19/1.28  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.19/1.28  tff(f_94, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.19/1.28  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.28  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.28  tff(c_26, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.28  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.28  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.28  tff(c_34, plain, (![A_27, B_28]: (r2_hidden(A_27, B_28) | v1_xboole_0(B_28) | ~m1_subset_1(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.28  tff(c_10, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.28  tff(c_45, plain, (![B_30, A_31]: (~r1_tarski(B_30, A_31) | v1_xboole_0(B_30) | ~m1_subset_1(A_31, B_30))), inference(resolution, [status(thm)], [c_34, c_10])).
% 2.19/1.28  tff(c_49, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_45])).
% 2.19/1.28  tff(c_50, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_49])).
% 2.19/1.28  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.28  tff(c_61, plain, (![A_38, B_39]: (m1_subset_1(o_2_1_compts_1(A_38, B_39), B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.28  tff(c_64, plain, (![A_38]: (m1_subset_1(o_2_1_compts_1(A_38, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_4, c_61])).
% 2.19/1.28  tff(c_68, plain, (![A_40]: (~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(negUnitSimplification, [status(thm)], [c_50, c_64])).
% 2.19/1.28  tff(c_71, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_30])).
% 2.19/1.28  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_71])).
% 2.19/1.28  tff(c_76, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_49])).
% 2.19/1.28  tff(c_93, plain, (![B_49, A_50]: (v2_tex_2(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~v1_xboole_0(B_49) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.28  tff(c_97, plain, (![A_50]: (v2_tex_2(k1_xboole_0, A_50) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(resolution, [status(thm)], [c_4, c_93])).
% 2.19/1.28  tff(c_100, plain, (![A_50]: (v2_tex_2(k1_xboole_0, A_50) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_97])).
% 2.19/1.28  tff(c_114, plain, (![A_57, B_58]: (m1_subset_1('#skF_1'(A_57, B_58), k1_zfmisc_1(u1_struct_0(A_57))) | ~v2_tex_2(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v3_tdlat_3(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.19/1.28  tff(c_22, plain, (![B_22]: (~v3_tex_2(B_22, '#skF_2') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.28  tff(c_129, plain, (![B_58]: (~v3_tex_2('#skF_1'('#skF_2', B_58), '#skF_2') | ~v2_tex_2(B_58, '#skF_2') | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_114, c_22])).
% 2.19/1.28  tff(c_137, plain, (![B_58]: (~v3_tex_2('#skF_1'('#skF_2', B_58), '#skF_2') | ~v2_tex_2(B_58, '#skF_2') | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_129])).
% 2.19/1.28  tff(c_139, plain, (![B_59]: (~v3_tex_2('#skF_1'('#skF_2', B_59), '#skF_2') | ~v2_tex_2(B_59, '#skF_2') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_137])).
% 2.19/1.28  tff(c_152, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2') | ~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_4, c_139])).
% 2.19/1.28  tff(c_154, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_152])).
% 2.19/1.28  tff(c_157, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_100, c_154])).
% 2.19/1.28  tff(c_160, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_157])).
% 2.19/1.28  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_160])).
% 2.19/1.28  tff(c_164, plain, (v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 2.19/1.28  tff(c_102, plain, (![A_52, B_53]: (v3_tex_2('#skF_1'(A_52, B_53), A_52) | ~v2_tex_2(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v3_tdlat_3(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.19/1.28  tff(c_106, plain, (![A_52]: (v3_tex_2('#skF_1'(A_52, k1_xboole_0), A_52) | ~v2_tex_2(k1_xboole_0, A_52) | ~l1_pre_topc(A_52) | ~v3_tdlat_3(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_4, c_102])).
% 2.19/1.28  tff(c_163, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 2.19/1.28  tff(c_167, plain, (~v2_tex_2(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_106, c_163])).
% 2.19/1.28  tff(c_170, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_164, c_167])).
% 2.19/1.28  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_170])).
% 2.19/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  Inference rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Ref     : 0
% 2.19/1.28  #Sup     : 23
% 2.19/1.28  #Fact    : 0
% 2.19/1.28  #Define  : 0
% 2.19/1.28  #Split   : 2
% 2.19/1.28  #Chain   : 0
% 2.19/1.28  #Close   : 0
% 2.19/1.28  
% 2.19/1.28  Ordering : KBO
% 2.19/1.28  
% 2.19/1.28  Simplification rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Subsume      : 2
% 2.19/1.28  #Demod        : 17
% 2.19/1.28  #Tautology    : 2
% 2.19/1.28  #SimpNegUnit  : 5
% 2.19/1.28  #BackRed      : 0
% 2.19/1.28  
% 2.19/1.28  #Partial instantiations: 0
% 2.19/1.28  #Strategies tried      : 1
% 2.19/1.28  
% 2.19/1.28  Timing (in seconds)
% 2.19/1.28  ----------------------
% 2.19/1.28  Preprocessing        : 0.28
% 2.19/1.28  Parsing              : 0.16
% 2.19/1.28  CNF conversion       : 0.02
% 2.19/1.28  Main loop            : 0.18
% 2.19/1.28  Inferencing          : 0.08
% 2.19/1.28  Reduction            : 0.05
% 2.19/1.28  Demodulation         : 0.03
% 2.19/1.28  BG Simplification    : 0.01
% 2.19/1.28  Subsumption          : 0.03
% 2.19/1.28  Abstraction          : 0.01
% 2.19/1.28  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.49
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
