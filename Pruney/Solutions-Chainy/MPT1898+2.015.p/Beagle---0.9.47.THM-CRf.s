%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:32 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 214 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_26] :
      ( v1_xboole_0(A_26)
      | r2_hidden('#skF_1'(A_26),A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [A_27] :
      ( ~ r1_tarski(A_27,'#skF_1'(A_27))
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_34,c_12])).

tff(c_48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [B_34,A_35] :
      ( v2_tex_2(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ v1_xboole_0(B_34)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_73,plain,(
    ! [A_36,A_37] :
      ( v2_tex_2(A_36,A_37)
      | ~ v1_xboole_0(A_36)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37)
      | ~ r1_tarski(A_36,u1_struct_0(A_37)) ) ),
    inference(resolution,[status(thm)],[c_10,c_67])).

tff(c_77,plain,(
    ! [A_37] :
      ( v2_tex_2(k1_xboole_0,A_37)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_80,plain,(
    ! [A_37] :
      ( v2_tex_2(k1_xboole_0,A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_77])).

tff(c_26,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    ! [A_39,B_40] :
      ( v3_tex_2('#skF_2'(A_39,B_40),A_39)
      | ~ v2_tex_2(B_40,A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v3_tdlat_3(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86,plain,(
    ! [A_39,A_6] :
      ( v3_tex_2('#skF_2'(A_39,A_6),A_39)
      | ~ v2_tex_2(A_6,A_39)
      | ~ l1_pre_topc(A_39)
      | ~ v3_tdlat_3(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39)
      | ~ r1_tarski(A_6,u1_struct_0(A_39)) ) ),
    inference(resolution,[status(thm)],[c_10,c_82])).

tff(c_99,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1('#skF_2'(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ v2_tex_2(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v3_tdlat_3(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [B_20] :
      ( ~ v3_tex_2(B_20,'#skF_3')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_113,plain,(
    ! [B_48] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_48),'#skF_3')
      | ~ v2_tex_2(B_48,'#skF_3')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_99,c_22])).

tff(c_120,plain,(
    ! [B_48] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_48),'#skF_3')
      | ~ v2_tex_2(B_48,'#skF_3')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_113])).

tff(c_122,plain,(
    ! [B_49] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_49),'#skF_3')
      | ~ v2_tex_2(B_49,'#skF_3')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_120])).

tff(c_136,plain,(
    ! [A_50] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',A_50),'#skF_3')
      | ~ v2_tex_2(A_50,'#skF_3')
      | ~ r1_tarski(A_50,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_122])).

tff(c_140,plain,(
    ! [A_6] :
      ( ~ v2_tex_2(A_6,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_86,c_136])).

tff(c_143,plain,(
    ! [A_6] :
      ( ~ v2_tex_2(A_6,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_140])).

tff(c_161,plain,(
    ! [A_53] :
      ( ~ v2_tex_2(A_53,'#skF_3')
      | ~ r1_tarski(A_53,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_143])).

tff(c_174,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_177,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_174])).

tff(c_180,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_177])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.81/1.22  
% 1.81/1.22  %Foreground sorts:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Background operators:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Foreground operators:
% 1.81/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.81/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.22  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.81/1.22  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.81/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.22  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.81/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.81/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.81/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.22  
% 2.09/1.23  tff(f_94, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.09/1.23  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.09/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.09/1.23  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.09/1.23  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.23  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.09/1.23  tff(f_79, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.09/1.23  tff(c_30, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.09/1.23  tff(c_28, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.09/1.23  tff(c_24, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.09/1.23  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.23  tff(c_34, plain, (![A_26]: (v1_xboole_0(A_26) | r2_hidden('#skF_1'(A_26), A_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.23  tff(c_12, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.23  tff(c_43, plain, (![A_27]: (~r1_tarski(A_27, '#skF_1'(A_27)) | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_34, c_12])).
% 2.09/1.23  tff(c_48, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_43])).
% 2.09/1.23  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.23  tff(c_67, plain, (![B_34, A_35]: (v2_tex_2(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~v1_xboole_0(B_34) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.23  tff(c_73, plain, (![A_36, A_37]: (v2_tex_2(A_36, A_37) | ~v1_xboole_0(A_36) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37) | ~r1_tarski(A_36, u1_struct_0(A_37)))), inference(resolution, [status(thm)], [c_10, c_67])).
% 2.09/1.23  tff(c_77, plain, (![A_37]: (v2_tex_2(k1_xboole_0, A_37) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(resolution, [status(thm)], [c_6, c_73])).
% 2.09/1.23  tff(c_80, plain, (![A_37]: (v2_tex_2(k1_xboole_0, A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_77])).
% 2.09/1.23  tff(c_26, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.09/1.23  tff(c_82, plain, (![A_39, B_40]: (v3_tex_2('#skF_2'(A_39, B_40), A_39) | ~v2_tex_2(B_40, A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v3_tdlat_3(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.09/1.23  tff(c_86, plain, (![A_39, A_6]: (v3_tex_2('#skF_2'(A_39, A_6), A_39) | ~v2_tex_2(A_6, A_39) | ~l1_pre_topc(A_39) | ~v3_tdlat_3(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39) | ~r1_tarski(A_6, u1_struct_0(A_39)))), inference(resolution, [status(thm)], [c_10, c_82])).
% 2.09/1.23  tff(c_99, plain, (![A_47, B_48]: (m1_subset_1('#skF_2'(A_47, B_48), k1_zfmisc_1(u1_struct_0(A_47))) | ~v2_tex_2(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v3_tdlat_3(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.09/1.23  tff(c_22, plain, (![B_20]: (~v3_tex_2(B_20, '#skF_3') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.09/1.23  tff(c_113, plain, (![B_48]: (~v3_tex_2('#skF_2'('#skF_3', B_48), '#skF_3') | ~v2_tex_2(B_48, '#skF_3') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_99, c_22])).
% 2.09/1.23  tff(c_120, plain, (![B_48]: (~v3_tex_2('#skF_2'('#skF_3', B_48), '#skF_3') | ~v2_tex_2(B_48, '#skF_3') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_113])).
% 2.09/1.23  tff(c_122, plain, (![B_49]: (~v3_tex_2('#skF_2'('#skF_3', B_49), '#skF_3') | ~v2_tex_2(B_49, '#skF_3') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_120])).
% 2.09/1.23  tff(c_136, plain, (![A_50]: (~v3_tex_2('#skF_2'('#skF_3', A_50), '#skF_3') | ~v2_tex_2(A_50, '#skF_3') | ~r1_tarski(A_50, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_122])).
% 2.09/1.23  tff(c_140, plain, (![A_6]: (~v2_tex_2(A_6, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_6, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_86, c_136])).
% 2.09/1.23  tff(c_143, plain, (![A_6]: (~v2_tex_2(A_6, '#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_6, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_140])).
% 2.09/1.23  tff(c_161, plain, (![A_53]: (~v2_tex_2(A_53, '#skF_3') | ~r1_tarski(A_53, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_30, c_143])).
% 2.09/1.23  tff(c_174, plain, (~v2_tex_2(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_6, c_161])).
% 2.09/1.23  tff(c_177, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_174])).
% 2.09/1.23  tff(c_180, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_177])).
% 2.09/1.23  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_180])).
% 2.09/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  Inference rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Ref     : 0
% 2.09/1.23  #Sup     : 25
% 2.09/1.23  #Fact    : 0
% 2.09/1.23  #Define  : 0
% 2.09/1.23  #Split   : 0
% 2.09/1.23  #Chain   : 0
% 2.09/1.23  #Close   : 0
% 2.09/1.23  
% 2.09/1.23  Ordering : KBO
% 2.09/1.23  
% 2.09/1.23  Simplification rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Subsume      : 2
% 2.09/1.23  #Demod        : 19
% 2.09/1.23  #Tautology    : 3
% 2.09/1.23  #SimpNegUnit  : 6
% 2.09/1.23  #BackRed      : 0
% 2.09/1.23  
% 2.09/1.23  #Partial instantiations: 0
% 2.09/1.23  #Strategies tried      : 1
% 2.09/1.23  
% 2.09/1.23  Timing (in seconds)
% 2.09/1.23  ----------------------
% 2.09/1.24  Preprocessing        : 0.27
% 2.09/1.24  Parsing              : 0.15
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.18
% 2.09/1.24  Inferencing          : 0.08
% 2.09/1.24  Reduction            : 0.04
% 2.09/1.24  Demodulation         : 0.03
% 2.09/1.24  BG Simplification    : 0.01
% 2.09/1.24  Subsumption          : 0.04
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.47
% 2.09/1.24  Index Insertion      : 0.00
% 2.09/1.24  Index Deletion       : 0.00
% 2.09/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
