%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:31 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 164 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   18
%              Number of atoms          :  146 ( 523 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_98,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [B_32,A_33] :
      ( m1_subset_1(B_32,A_33)
      | ~ r2_hidden(B_32,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    ! [A_11,B_13] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_11),B_13),A_11)
      | ~ m1_subset_1(B_13,u1_struct_0(A_11))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k6_domain_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    ! [A_44,B_45] :
      ( v3_tex_2('#skF_2'(A_44,B_45),A_44)
      | ~ v2_tex_2(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v3_tdlat_3(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_232,plain,(
    ! [A_66,B_67] :
      ( v3_tex_2('#skF_2'(A_66,k6_domain_1(u1_struct_0(A_66),B_67)),A_66)
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_66),B_67),A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v3_tdlat_3(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ m1_subset_1(B_67,u1_struct_0(A_66))
      | v1_xboole_0(u1_struct_0(A_66)) ) ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_124,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1('#skF_2'(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v2_tex_2(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v3_tdlat_3(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [B_21] :
      ( ~ v3_tex_2(B_21,'#skF_3')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_132,plain,(
    ! [B_51] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_51),'#skF_3')
      | ~ v2_tex_2(B_51,'#skF_3')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_124,c_28])).

tff(c_140,plain,(
    ! [B_51] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_51),'#skF_3')
      | ~ v2_tex_2(B_51,'#skF_3')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_132])).

tff(c_143,plain,(
    ! [B_52] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_52),'#skF_3')
      | ~ v2_tex_2(B_52,'#skF_3')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_140])).

tff(c_164,plain,(
    ! [B_10] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_10)),'#skF_3')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_10),'#skF_3')
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_143])).

tff(c_171,plain,(
    ! [B_10] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_10)),'#skF_3')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_10),'#skF_3')
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_236,plain,(
    ! [B_67] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_67),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_232,c_171])).

tff(c_239,plain,(
    ! [B_67] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_67),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_236])).

tff(c_240,plain,(
    ! [B_67] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_67),'#skF_3')
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_239])).

tff(c_242,plain,(
    ! [B_68] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_68),'#skF_3')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_246,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_242])).

tff(c_249,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_246])).

tff(c_251,plain,(
    ! [B_69] : ~ m1_subset_1(B_69,u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_249])).

tff(c_260,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_61,c_251])).

tff(c_16,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_264,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_260,c_16])).

tff(c_267,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_264])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_267])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_271])).

tff(c_276,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_279,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_16])).

tff(c_282,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_279])).

tff(c_285,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_282])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_285])).

tff(c_290,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_293,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_16])).

tff(c_296,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_293])).

tff(c_299,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_296])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:49:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2
% 2.24/1.30  
% 2.24/1.30  %Foreground sorts:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Background operators:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Foreground operators:
% 2.24/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.24/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.24/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.30  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.24/1.30  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.24/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.24/1.30  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.30  
% 2.53/1.32  tff(f_113, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.53/1.32  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.53/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.53/1.32  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.53/1.32  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.53/1.32  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.53/1.32  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.53/1.32  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.53/1.32  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.32  tff(c_14, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.53/1.32  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.32  tff(c_57, plain, (![B_32, A_33]: (m1_subset_1(B_32, A_33) | ~r2_hidden(B_32, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.32  tff(c_61, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_57])).
% 2.53/1.32  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.32  tff(c_20, plain, (![A_11, B_13]: (v2_tex_2(k6_domain_1(u1_struct_0(A_11), B_13), A_11) | ~m1_subset_1(B_13, u1_struct_0(A_11)) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.32  tff(c_32, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.32  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(k6_domain_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.53/1.32  tff(c_97, plain, (![A_44, B_45]: (v3_tex_2('#skF_2'(A_44, B_45), A_44) | ~v2_tex_2(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v3_tdlat_3(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.53/1.32  tff(c_232, plain, (![A_66, B_67]: (v3_tex_2('#skF_2'(A_66, k6_domain_1(u1_struct_0(A_66), B_67)), A_66) | ~v2_tex_2(k6_domain_1(u1_struct_0(A_66), B_67), A_66) | ~l1_pre_topc(A_66) | ~v3_tdlat_3(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66) | ~m1_subset_1(B_67, u1_struct_0(A_66)) | v1_xboole_0(u1_struct_0(A_66)))), inference(resolution, [status(thm)], [c_18, c_97])).
% 2.53/1.32  tff(c_124, plain, (![A_50, B_51]: (m1_subset_1('#skF_2'(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~v2_tex_2(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v3_tdlat_3(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.53/1.32  tff(c_28, plain, (![B_21]: (~v3_tex_2(B_21, '#skF_3') | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.32  tff(c_132, plain, (![B_51]: (~v3_tex_2('#skF_2'('#skF_3', B_51), '#skF_3') | ~v2_tex_2(B_51, '#skF_3') | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_124, c_28])).
% 2.53/1.32  tff(c_140, plain, (![B_51]: (~v3_tex_2('#skF_2'('#skF_3', B_51), '#skF_3') | ~v2_tex_2(B_51, '#skF_3') | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_132])).
% 2.53/1.32  tff(c_143, plain, (![B_52]: (~v3_tex_2('#skF_2'('#skF_3', B_52), '#skF_3') | ~v2_tex_2(B_52, '#skF_3') | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_140])).
% 2.53/1.32  tff(c_164, plain, (![B_10]: (~v3_tex_2('#skF_2'('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_10)), '#skF_3') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_10), '#skF_3') | ~m1_subset_1(B_10, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_143])).
% 2.53/1.32  tff(c_171, plain, (![B_10]: (~v3_tex_2('#skF_2'('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_10)), '#skF_3') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_10), '#skF_3') | ~m1_subset_1(B_10, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_164])).
% 2.53/1.32  tff(c_236, plain, (![B_67]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_67), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_67, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_232, c_171])).
% 2.53/1.32  tff(c_239, plain, (![B_67]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_67), '#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_67, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_236])).
% 2.53/1.32  tff(c_240, plain, (![B_67]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_67), '#skF_3') | ~m1_subset_1(B_67, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_239])).
% 2.53/1.32  tff(c_242, plain, (![B_68]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_68), '#skF_3') | ~m1_subset_1(B_68, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_240])).
% 2.53/1.32  tff(c_246, plain, (![B_13]: (~m1_subset_1(B_13, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_242])).
% 2.53/1.32  tff(c_249, plain, (![B_13]: (~m1_subset_1(B_13, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_246])).
% 2.53/1.32  tff(c_251, plain, (![B_69]: (~m1_subset_1(B_69, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_249])).
% 2.53/1.32  tff(c_260, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_61, c_251])).
% 2.53/1.32  tff(c_16, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.32  tff(c_264, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_260, c_16])).
% 2.53/1.32  tff(c_267, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_264])).
% 2.53/1.32  tff(c_271, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_267])).
% 2.53/1.32  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_271])).
% 2.53/1.32  tff(c_276, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_240])).
% 2.53/1.32  tff(c_279, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_276, c_16])).
% 2.53/1.32  tff(c_282, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_279])).
% 2.53/1.32  tff(c_285, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_282])).
% 2.53/1.32  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_285])).
% 2.53/1.32  tff(c_290, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_164])).
% 2.53/1.32  tff(c_293, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_290, c_16])).
% 2.53/1.32  tff(c_296, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_293])).
% 2.53/1.32  tff(c_299, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_296])).
% 2.53/1.32  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_299])).
% 2.53/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  Inference rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Ref     : 0
% 2.53/1.32  #Sup     : 43
% 2.53/1.32  #Fact    : 0
% 2.53/1.32  #Define  : 0
% 2.53/1.32  #Split   : 6
% 2.53/1.32  #Chain   : 0
% 2.53/1.32  #Close   : 0
% 2.53/1.32  
% 2.53/1.32  Ordering : KBO
% 2.53/1.32  
% 2.53/1.32  Simplification rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Subsume      : 9
% 2.53/1.32  #Demod        : 20
% 2.53/1.32  #Tautology    : 6
% 2.53/1.32  #SimpNegUnit  : 12
% 2.53/1.32  #BackRed      : 0
% 2.53/1.32  
% 2.53/1.32  #Partial instantiations: 0
% 2.53/1.32  #Strategies tried      : 1
% 2.53/1.32  
% 2.53/1.32  Timing (in seconds)
% 2.53/1.32  ----------------------
% 2.53/1.32  Preprocessing        : 0.29
% 2.53/1.32  Parsing              : 0.17
% 2.53/1.32  CNF conversion       : 0.02
% 2.53/1.32  Main loop            : 0.26
% 2.53/1.32  Inferencing          : 0.11
% 2.53/1.32  Reduction            : 0.06
% 2.53/1.32  Demodulation         : 0.04
% 2.53/1.32  BG Simplification    : 0.01
% 2.53/1.32  Subsumption          : 0.05
% 2.53/1.32  Abstraction          : 0.01
% 2.53/1.32  MUC search           : 0.00
% 2.53/1.32  Cooper               : 0.00
% 2.53/1.32  Total                : 0.58
% 2.53/1.32  Index Insertion      : 0.00
% 2.53/1.32  Index Deletion       : 0.00
% 2.53/1.32  Index Matching       : 0.00
% 2.53/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
