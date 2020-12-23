%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:11 EST 2020

% Result     : Theorem 9.45s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 104 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 228 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_67,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_88,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_99,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_101,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_99,c_101])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_347,plain,(
    ! [C_68,A_69,B_70] :
      ( v2_tex_2(C_68,A_69)
      | ~ v2_tex_2(B_70,A_69)
      | ~ r1_tarski(C_68,B_70)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_797,plain,(
    ! [A_108,B_109,A_110] :
      ( v2_tex_2(k3_xboole_0(A_108,B_109),A_110)
      | ~ v2_tex_2(A_108,A_110)
      | ~ m1_subset_1(k3_xboole_0(A_108,B_109),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(A_108,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_4,c_347])).

tff(c_1125,plain,(
    ! [A_131,B_132,A_133] :
      ( v2_tex_2(k3_xboole_0(A_131,B_132),A_133)
      | ~ v2_tex_2(A_131,A_133)
      | ~ m1_subset_1(A_131,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ r1_tarski(k3_xboole_0(A_131,B_132),u1_struct_0(A_133)) ) ),
    inference(resolution,[status(thm)],[c_14,c_797])).

tff(c_1189,plain,(
    ! [A_131,B_132] :
      ( v2_tex_2(k3_xboole_0(A_131,B_132),'#skF_1')
      | ~ v2_tex_2(A_131,'#skF_1')
      | ~ m1_subset_1(A_131,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_131,B_132),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_111,c_1125])).

tff(c_7029,plain,(
    ! [A_282,B_283] :
      ( v2_tex_2(k3_xboole_0(A_282,B_283),'#skF_1')
      | ~ v2_tex_2(A_282,'#skF_1')
      | ~ m1_subset_1(A_282,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_282,B_283),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1189])).

tff(c_7036,plain,(
    ! [B_283] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_283),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_283),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_7029])).

tff(c_7045,plain,(
    ! [B_284] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_284),'#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_284),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_7036])).

tff(c_7062,plain,(
    ! [B_285] :
      ( v2_tex_2(k3_xboole_0(B_285,'#skF_2'),'#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_285),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7045])).

tff(c_244,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(A_57,B_58,C_59) = k3_xboole_0(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_252,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),B_58,'#skF_3') = k3_xboole_0(B_58,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_244])).

tff(c_18,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_286,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_18])).

tff(c_287,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_286])).

tff(c_7065,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7062,c_287])).

tff(c_7089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_7065])).

tff(c_7090,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_7102,plain,(
    ! [A_288,B_289] :
      ( r1_tarski(A_288,B_289)
      | ~ m1_subset_1(A_288,k1_zfmisc_1(B_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7109,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_7102])).

tff(c_7125,plain,(
    ! [A_294,C_295,B_296] :
      ( r1_tarski(A_294,C_295)
      | ~ r1_tarski(B_296,C_295)
      | ~ r1_tarski(A_294,B_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7135,plain,(
    ! [A_294] :
      ( r1_tarski(A_294,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_294,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7109,c_7125])).

tff(c_7287,plain,(
    ! [C_318,A_319,B_320] :
      ( v2_tex_2(C_318,A_319)
      | ~ v2_tex_2(B_320,A_319)
      | ~ r1_tarski(C_318,B_320)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7682,plain,(
    ! [A_354,B_355,A_356] :
      ( v2_tex_2(k3_xboole_0(A_354,B_355),A_356)
      | ~ v2_tex_2(A_354,A_356)
      | ~ m1_subset_1(k3_xboole_0(A_354,B_355),k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ m1_subset_1(A_354,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ l1_pre_topc(A_356) ) ),
    inference(resolution,[status(thm)],[c_4,c_7287])).

tff(c_8090,plain,(
    ! [A_385,B_386,A_387] :
      ( v2_tex_2(k3_xboole_0(A_385,B_386),A_387)
      | ~ v2_tex_2(A_385,A_387)
      | ~ m1_subset_1(A_385,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l1_pre_topc(A_387)
      | ~ r1_tarski(k3_xboole_0(A_385,B_386),u1_struct_0(A_387)) ) ),
    inference(resolution,[status(thm)],[c_14,c_7682])).

tff(c_8154,plain,(
    ! [A_385,B_386] :
      ( v2_tex_2(k3_xboole_0(A_385,B_386),'#skF_1')
      | ~ v2_tex_2(A_385,'#skF_1')
      | ~ m1_subset_1(A_385,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_385,B_386),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7135,c_8090])).

tff(c_14355,plain,(
    ! [A_547,B_548] :
      ( v2_tex_2(k3_xboole_0(A_547,B_548),'#skF_1')
      | ~ v2_tex_2(A_547,'#skF_1')
      | ~ m1_subset_1(A_547,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_547,B_548),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8154])).

tff(c_14360,plain,(
    ! [B_548] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_548),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_548),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_14355])).

tff(c_14366,plain,(
    ! [B_548] : v2_tex_2(k3_xboole_0('#skF_3',B_548),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7090,c_14360])).

tff(c_7186,plain,(
    ! [A_305,B_306,C_307] :
      ( k9_subset_1(A_305,B_306,C_307) = k3_xboole_0(B_306,C_307)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(A_305)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7194,plain,(
    ! [B_306] : k9_subset_1(u1_struct_0('#skF_1'),B_306,'#skF_3') = k3_xboole_0(B_306,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_7186])).

tff(c_7319,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7194,c_18])).

tff(c_7320,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7319])).

tff(c_14370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14366,c_7320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.45/3.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.30  
% 9.45/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.31  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 9.45/3.31  
% 9.45/3.31  %Foreground sorts:
% 9.45/3.31  
% 9.45/3.31  
% 9.45/3.31  %Background operators:
% 9.45/3.31  
% 9.45/3.31  
% 9.45/3.31  %Foreground operators:
% 9.45/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.45/3.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.45/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.45/3.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.45/3.31  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.45/3.31  tff('#skF_2', type, '#skF_2': $i).
% 9.45/3.31  tff('#skF_3', type, '#skF_3': $i).
% 9.45/3.31  tff('#skF_1', type, '#skF_1': $i).
% 9.45/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.45/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.45/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.45/3.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.45/3.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.45/3.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.45/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.45/3.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.45/3.31  
% 9.45/3.32  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.45/3.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.45/3.32  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 9.45/3.32  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.45/3.32  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.45/3.32  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 9.45/3.32  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.45/3.32  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.45/3.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.45/3.32  tff(c_20, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.45/3.32  tff(c_67, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 9.45/3.32  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.45/3.32  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.45/3.32  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.45/3.32  tff(c_88, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.45/3.32  tff(c_99, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_88])).
% 9.45/3.32  tff(c_101, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/3.32  tff(c_111, plain, (![A_38]: (r1_tarski(A_38, u1_struct_0('#skF_1')) | ~r1_tarski(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_99, c_101])).
% 9.45/3.32  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.45/3.32  tff(c_347, plain, (![C_68, A_69, B_70]: (v2_tex_2(C_68, A_69) | ~v2_tex_2(B_70, A_69) | ~r1_tarski(C_68, B_70) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.45/3.32  tff(c_797, plain, (![A_108, B_109, A_110]: (v2_tex_2(k3_xboole_0(A_108, B_109), A_110) | ~v2_tex_2(A_108, A_110) | ~m1_subset_1(k3_xboole_0(A_108, B_109), k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(A_108, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_4, c_347])).
% 9.45/3.32  tff(c_1125, plain, (![A_131, B_132, A_133]: (v2_tex_2(k3_xboole_0(A_131, B_132), A_133) | ~v2_tex_2(A_131, A_133) | ~m1_subset_1(A_131, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~r1_tarski(k3_xboole_0(A_131, B_132), u1_struct_0(A_133)))), inference(resolution, [status(thm)], [c_14, c_797])).
% 9.45/3.32  tff(c_1189, plain, (![A_131, B_132]: (v2_tex_2(k3_xboole_0(A_131, B_132), '#skF_1') | ~v2_tex_2(A_131, '#skF_1') | ~m1_subset_1(A_131, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_131, B_132), '#skF_3'))), inference(resolution, [status(thm)], [c_111, c_1125])).
% 9.45/3.32  tff(c_7029, plain, (![A_282, B_283]: (v2_tex_2(k3_xboole_0(A_282, B_283), '#skF_1') | ~v2_tex_2(A_282, '#skF_1') | ~m1_subset_1(A_282, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_282, B_283), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1189])).
% 9.45/3.32  tff(c_7036, plain, (![B_283]: (v2_tex_2(k3_xboole_0('#skF_2', B_283), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_283), '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_7029])).
% 9.45/3.32  tff(c_7045, plain, (![B_284]: (v2_tex_2(k3_xboole_0('#skF_2', B_284), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_284), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_7036])).
% 9.45/3.32  tff(c_7062, plain, (![B_285]: (v2_tex_2(k3_xboole_0(B_285, '#skF_2'), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_285), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7045])).
% 9.45/3.32  tff(c_244, plain, (![A_57, B_58, C_59]: (k9_subset_1(A_57, B_58, C_59)=k3_xboole_0(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.45/3.32  tff(c_252, plain, (![B_58]: (k9_subset_1(u1_struct_0('#skF_1'), B_58, '#skF_3')=k3_xboole_0(B_58, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_244])).
% 9.45/3.32  tff(c_18, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.45/3.32  tff(c_286, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_18])).
% 9.45/3.32  tff(c_287, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_286])).
% 9.45/3.32  tff(c_7065, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_7062, c_287])).
% 9.45/3.32  tff(c_7089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_7065])).
% 9.45/3.32  tff(c_7090, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 9.45/3.32  tff(c_7102, plain, (![A_288, B_289]: (r1_tarski(A_288, B_289) | ~m1_subset_1(A_288, k1_zfmisc_1(B_289)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.45/3.32  tff(c_7109, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_7102])).
% 9.45/3.32  tff(c_7125, plain, (![A_294, C_295, B_296]: (r1_tarski(A_294, C_295) | ~r1_tarski(B_296, C_295) | ~r1_tarski(A_294, B_296))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/3.32  tff(c_7135, plain, (![A_294]: (r1_tarski(A_294, u1_struct_0('#skF_1')) | ~r1_tarski(A_294, '#skF_3'))), inference(resolution, [status(thm)], [c_7109, c_7125])).
% 9.45/3.32  tff(c_7287, plain, (![C_318, A_319, B_320]: (v2_tex_2(C_318, A_319) | ~v2_tex_2(B_320, A_319) | ~r1_tarski(C_318, B_320) | ~m1_subset_1(C_318, k1_zfmisc_1(u1_struct_0(A_319))) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_319))) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.45/3.32  tff(c_7682, plain, (![A_354, B_355, A_356]: (v2_tex_2(k3_xboole_0(A_354, B_355), A_356) | ~v2_tex_2(A_354, A_356) | ~m1_subset_1(k3_xboole_0(A_354, B_355), k1_zfmisc_1(u1_struct_0(A_356))) | ~m1_subset_1(A_354, k1_zfmisc_1(u1_struct_0(A_356))) | ~l1_pre_topc(A_356))), inference(resolution, [status(thm)], [c_4, c_7287])).
% 9.45/3.32  tff(c_8090, plain, (![A_385, B_386, A_387]: (v2_tex_2(k3_xboole_0(A_385, B_386), A_387) | ~v2_tex_2(A_385, A_387) | ~m1_subset_1(A_385, k1_zfmisc_1(u1_struct_0(A_387))) | ~l1_pre_topc(A_387) | ~r1_tarski(k3_xboole_0(A_385, B_386), u1_struct_0(A_387)))), inference(resolution, [status(thm)], [c_14, c_7682])).
% 9.45/3.32  tff(c_8154, plain, (![A_385, B_386]: (v2_tex_2(k3_xboole_0(A_385, B_386), '#skF_1') | ~v2_tex_2(A_385, '#skF_1') | ~m1_subset_1(A_385, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_385, B_386), '#skF_3'))), inference(resolution, [status(thm)], [c_7135, c_8090])).
% 9.45/3.32  tff(c_14355, plain, (![A_547, B_548]: (v2_tex_2(k3_xboole_0(A_547, B_548), '#skF_1') | ~v2_tex_2(A_547, '#skF_1') | ~m1_subset_1(A_547, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_547, B_548), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8154])).
% 9.45/3.32  tff(c_14360, plain, (![B_548]: (v2_tex_2(k3_xboole_0('#skF_3', B_548), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', B_548), '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_14355])).
% 9.45/3.32  tff(c_14366, plain, (![B_548]: (v2_tex_2(k3_xboole_0('#skF_3', B_548), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7090, c_14360])).
% 9.45/3.32  tff(c_7186, plain, (![A_305, B_306, C_307]: (k9_subset_1(A_305, B_306, C_307)=k3_xboole_0(B_306, C_307) | ~m1_subset_1(C_307, k1_zfmisc_1(A_305)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.45/3.32  tff(c_7194, plain, (![B_306]: (k9_subset_1(u1_struct_0('#skF_1'), B_306, '#skF_3')=k3_xboole_0(B_306, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_7186])).
% 9.45/3.32  tff(c_7319, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7194, c_18])).
% 9.45/3.32  tff(c_7320, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7319])).
% 9.45/3.32  tff(c_14370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14366, c_7320])).
% 9.45/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.32  
% 9.45/3.32  Inference rules
% 9.45/3.32  ----------------------
% 9.45/3.32  #Ref     : 0
% 9.45/3.32  #Sup     : 3592
% 9.45/3.32  #Fact    : 0
% 9.45/3.32  #Define  : 0
% 9.45/3.32  #Split   : 10
% 9.45/3.32  #Chain   : 0
% 9.45/3.32  #Close   : 0
% 9.45/3.32  
% 9.45/3.32  Ordering : KBO
% 9.45/3.32  
% 9.45/3.32  Simplification rules
% 9.45/3.32  ----------------------
% 9.45/3.32  #Subsume      : 462
% 9.45/3.32  #Demod        : 1131
% 9.45/3.32  #Tautology    : 1241
% 9.45/3.32  #SimpNegUnit  : 4
% 9.45/3.32  #BackRed      : 3
% 9.45/3.32  
% 9.45/3.32  #Partial instantiations: 0
% 9.45/3.32  #Strategies tried      : 1
% 9.45/3.32  
% 9.45/3.32  Timing (in seconds)
% 9.45/3.32  ----------------------
% 9.45/3.32  Preprocessing        : 0.29
% 9.45/3.32  Parsing              : 0.16
% 9.45/3.32  CNF conversion       : 0.02
% 9.45/3.32  Main loop            : 2.25
% 9.45/3.32  Inferencing          : 0.52
% 9.45/3.32  Reduction            : 1.18
% 9.45/3.32  Demodulation         : 1.05
% 9.45/3.32  BG Simplification    : 0.06
% 9.45/3.32  Subsumption          : 0.36
% 9.45/3.32  Abstraction          : 0.08
% 9.45/3.32  MUC search           : 0.00
% 9.45/3.32  Cooper               : 0.00
% 9.45/3.32  Total                : 2.57
% 9.45/3.32  Index Insertion      : 0.00
% 9.45/3.32  Index Deletion       : 0.00
% 9.45/3.32  Index Matching       : 0.00
% 9.45/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
