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
% DateTime   : Thu Dec  3 10:30:31 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 221 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_80,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_2'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( ~ v1_xboole_0(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [B_45,A_46] :
      ( v2_tex_2(B_45,A_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ v1_xboole_0(B_45)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [A_64,A_65] :
      ( v2_tex_2(A_64,A_65)
      | ~ v1_xboole_0(A_64)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | ~ r1_tarski(A_64,u1_struct_0(A_65)) ) ),
    inference(resolution,[status(thm)],[c_16,c_93])).

tff(c_157,plain,(
    ! [A_32,A_65] :
      ( v2_tex_2(A_32,A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_58,c_147])).

tff(c_30,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_142,plain,(
    ! [A_62,B_63] :
      ( v3_tex_2('#skF_3'(A_62,B_63),A_62)
      | ~ v2_tex_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v3_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_146,plain,(
    ! [A_62,A_10] :
      ( v3_tex_2('#skF_3'(A_62,A_10),A_62)
      | ~ v2_tex_2(A_10,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v3_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62)
      | ~ r1_tarski(A_10,u1_struct_0(A_62)) ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_192,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1('#skF_3'(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v3_tdlat_3(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [B_22] :
      ( ~ v3_tex_2(B_22,'#skF_4')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_200,plain,(
    ! [B_74] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_74),'#skF_4')
      | ~ v2_tex_2(B_74,'#skF_4')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_192,c_26])).

tff(c_208,plain,(
    ! [B_74] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_74),'#skF_4')
      | ~ v2_tex_2(B_74,'#skF_4')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_200])).

tff(c_212,plain,(
    ! [B_76] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_76),'#skF_4')
      | ~ v2_tex_2(B_76,'#skF_4')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_208])).

tff(c_226,plain,(
    ! [A_77] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',A_77),'#skF_4')
      | ~ v2_tex_2(A_77,'#skF_4')
      | ~ r1_tarski(A_77,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_230,plain,(
    ! [A_10] :
      ( ~ v2_tex_2(A_10,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_10,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_146,c_226])).

tff(c_233,plain,(
    ! [A_10] :
      ( ~ v2_tex_2(A_10,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_10,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_230])).

tff(c_235,plain,(
    ! [A_78] :
      ( ~ v2_tex_2(A_78,'#skF_4')
      | ~ r1_tarski(A_78,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_233])).

tff(c_246,plain,(
    ! [A_79] :
      ( ~ v2_tex_2(A_79,'#skF_4')
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_58,c_235])).

tff(c_250,plain,(
    ! [A_32] :
      ( ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_157,c_246])).

tff(c_253,plain,(
    ! [A_32] :
      ( v2_struct_0('#skF_4')
      | ~ v1_xboole_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_250])).

tff(c_254,plain,(
    ! [A_32] : ~ v1_xboole_0(A_32) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_253])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:19:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.17/1.26  
% 2.17/1.26  %Foreground sorts:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Background operators:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Foreground operators:
% 2.17/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.17/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.17/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.26  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.17/1.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.17/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.26  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.17/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.26  
% 2.17/1.27  tff(f_95, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.17/1.27  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.17/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.17/1.27  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.27  tff(f_57, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.17/1.27  tff(f_80, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.17/1.27  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.27  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.17/1.27  tff(c_32, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.17/1.27  tff(c_28, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.17/1.27  tff(c_54, plain, (![A_32, B_33]: (r2_hidden('#skF_2'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_58, plain, (![A_32, B_33]: (~v1_xboole_0(A_32) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.17/1.27  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.27  tff(c_93, plain, (![B_45, A_46]: (v2_tex_2(B_45, A_46) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~v1_xboole_0(B_45) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.27  tff(c_147, plain, (![A_64, A_65]: (v2_tex_2(A_64, A_65) | ~v1_xboole_0(A_64) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | ~r1_tarski(A_64, u1_struct_0(A_65)))), inference(resolution, [status(thm)], [c_16, c_93])).
% 2.17/1.27  tff(c_157, plain, (![A_32, A_65]: (v2_tex_2(A_32, A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_58, c_147])).
% 2.17/1.27  tff(c_30, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.17/1.27  tff(c_142, plain, (![A_62, B_63]: (v3_tex_2('#skF_3'(A_62, B_63), A_62) | ~v2_tex_2(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v3_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.17/1.27  tff(c_146, plain, (![A_62, A_10]: (v3_tex_2('#skF_3'(A_62, A_10), A_62) | ~v2_tex_2(A_10, A_62) | ~l1_pre_topc(A_62) | ~v3_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62) | ~r1_tarski(A_10, u1_struct_0(A_62)))), inference(resolution, [status(thm)], [c_16, c_142])).
% 2.17/1.27  tff(c_192, plain, (![A_73, B_74]: (m1_subset_1('#skF_3'(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v3_tdlat_3(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.17/1.27  tff(c_26, plain, (![B_22]: (~v3_tex_2(B_22, '#skF_4') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.17/1.27  tff(c_200, plain, (![B_74]: (~v3_tex_2('#skF_3'('#skF_4', B_74), '#skF_4') | ~v2_tex_2(B_74, '#skF_4') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_192, c_26])).
% 2.17/1.27  tff(c_208, plain, (![B_74]: (~v3_tex_2('#skF_3'('#skF_4', B_74), '#skF_4') | ~v2_tex_2(B_74, '#skF_4') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_200])).
% 2.17/1.27  tff(c_212, plain, (![B_76]: (~v3_tex_2('#skF_3'('#skF_4', B_76), '#skF_4') | ~v2_tex_2(B_76, '#skF_4') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_208])).
% 2.17/1.27  tff(c_226, plain, (![A_77]: (~v3_tex_2('#skF_3'('#skF_4', A_77), '#skF_4') | ~v2_tex_2(A_77, '#skF_4') | ~r1_tarski(A_77, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_212])).
% 2.17/1.27  tff(c_230, plain, (![A_10]: (~v2_tex_2(A_10, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_10, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_146, c_226])).
% 2.17/1.27  tff(c_233, plain, (![A_10]: (~v2_tex_2(A_10, '#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_10, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_230])).
% 2.17/1.27  tff(c_235, plain, (![A_78]: (~v2_tex_2(A_78, '#skF_4') | ~r1_tarski(A_78, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_34, c_233])).
% 2.17/1.27  tff(c_246, plain, (![A_79]: (~v2_tex_2(A_79, '#skF_4') | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_58, c_235])).
% 2.17/1.27  tff(c_250, plain, (![A_32]: (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_157, c_246])).
% 2.17/1.27  tff(c_253, plain, (![A_32]: (v2_struct_0('#skF_4') | ~v1_xboole_0(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_250])).
% 2.17/1.27  tff(c_254, plain, (![A_32]: (~v1_xboole_0(A_32))), inference(negUnitSimplification, [status(thm)], [c_34, c_253])).
% 2.17/1.27  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.27  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_12])).
% 2.17/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  Inference rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Ref     : 0
% 2.17/1.27  #Sup     : 41
% 2.17/1.27  #Fact    : 0
% 2.17/1.27  #Define  : 0
% 2.17/1.27  #Split   : 1
% 2.17/1.27  #Chain   : 0
% 2.17/1.27  #Close   : 0
% 2.17/1.27  
% 2.17/1.27  Ordering : KBO
% 2.17/1.27  
% 2.17/1.27  Simplification rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Subsume      : 21
% 2.17/1.27  #Demod        : 16
% 2.17/1.27  #Tautology    : 5
% 2.17/1.27  #SimpNegUnit  : 11
% 2.17/1.27  #BackRed      : 4
% 2.17/1.27  
% 2.17/1.27  #Partial instantiations: 0
% 2.17/1.27  #Strategies tried      : 1
% 2.17/1.27  
% 2.17/1.27  Timing (in seconds)
% 2.17/1.27  ----------------------
% 2.17/1.27  Preprocessing        : 0.29
% 2.17/1.27  Parsing              : 0.16
% 2.17/1.28  CNF conversion       : 0.02
% 2.17/1.28  Main loop            : 0.23
% 2.17/1.28  Inferencing          : 0.10
% 2.17/1.28  Reduction            : 0.05
% 2.17/1.28  Demodulation         : 0.04
% 2.17/1.28  BG Simplification    : 0.01
% 2.17/1.28  Subsumption          : 0.05
% 2.17/1.28  Abstraction          : 0.01
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.56
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.28  Index Deletion       : 0.00
% 2.17/1.28  Index Matching       : 0.00
% 2.17/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
