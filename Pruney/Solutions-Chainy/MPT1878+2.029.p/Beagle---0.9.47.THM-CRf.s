%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 8.21s
% Output     : CNFRefutation 8.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 111 expanded)
%              Number of leaves         :   36 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  202 ( 332 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_103,axiom,(
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

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_59] :
      ( m1_subset_1('#skF_2'(A_59),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_228,plain,(
    ! [A_76,A_77] :
      ( m1_subset_1(A_76,u1_struct_0(A_77))
      | ~ r2_hidden(A_76,'#skF_2'(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_144,c_16])).

tff(c_233,plain,(
    ! [A_77] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_77)),u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77)
      | v1_xboole_0('#skF_2'(A_77)) ) ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_354,plain,(
    ! [A_89] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_89)),u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89)
      | v1_xboole_0('#skF_2'(A_89)) ) ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k6_domain_1(A_19,B_20) = k1_tarski(B_20)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_880,plain,(
    ! [A_134] :
      ( k6_domain_1(u1_struct_0(A_134),'#skF_1'('#skF_2'(A_134))) = k1_tarski('#skF_1'('#skF_2'(A_134)))
      | v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0('#skF_2'(A_134)) ) ),
    inference(resolution,[status(thm)],[c_354,c_28])).

tff(c_42,plain,(
    ! [A_31,B_33] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_31),B_33),A_31)
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_901,plain,(
    ! [A_134] :
      ( v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_134))),A_134)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_134)),u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0('#skF_2'(A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_42])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k6_domain_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3037,plain,(
    ! [A_235] :
      ( m1_subset_1(k1_tarski('#skF_1'('#skF_2'(A_235))),k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_235)),u1_struct_0(A_235))
      | v1_xboole_0(u1_struct_0(A_235))
      | v1_xboole_0(u1_struct_0(A_235))
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235)
      | v1_xboole_0('#skF_2'(A_235)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_26])).

tff(c_57,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_57])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_396,plain,(
    ! [C_92,B_93,A_94] :
      ( C_92 = B_93
      | ~ r1_tarski(B_93,C_92)
      | ~ v2_tex_2(C_92,A_94)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v3_tex_2(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_398,plain,(
    ! [A_6,A_94] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_94)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v3_tex_2('#skF_5',A_94)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_68,c_396])).

tff(c_401,plain,(
    ! [A_6,A_94] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_94)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v3_tex_2('#skF_5',A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_398])).

tff(c_5221,plain,(
    ! [A_301] :
      ( k1_tarski('#skF_1'('#skF_2'(A_301))) = '#skF_5'
      | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_301))),A_301)
      | ~ v3_tex_2('#skF_5',A_301)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_301)),u1_struct_0(A_301))
      | v1_xboole_0(u1_struct_0(A_301))
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301)
      | v1_xboole_0('#skF_2'(A_301)) ) ),
    inference(resolution,[status(thm)],[c_3037,c_401])).

tff(c_5226,plain,(
    ! [A_302] :
      ( k1_tarski('#skF_1'('#skF_2'(A_302))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_302)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_302)),u1_struct_0(A_302))
      | v1_xboole_0(u1_struct_0(A_302))
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302)
      | v1_xboole_0('#skF_2'(A_302)) ) ),
    inference(resolution,[status(thm)],[c_901,c_5221])).

tff(c_5307,plain,(
    ! [A_306] :
      ( k1_tarski('#skF_1'('#skF_2'(A_306))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_306)
      | v1_xboole_0(u1_struct_0(A_306))
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306)
      | v1_xboole_0('#skF_2'(A_306)) ) ),
    inference(resolution,[status(thm)],[c_233,c_5226])).

tff(c_12,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5329,plain,(
    ! [A_306] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ v3_tex_2('#skF_5',A_306)
      | v1_xboole_0(u1_struct_0(A_306))
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306)
      | v1_xboole_0('#skF_2'(A_306)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5307,c_12])).

tff(c_5338,plain,(
    ! [A_307] :
      ( ~ v3_tex_2('#skF_5',A_307)
      | v1_xboole_0(u1_struct_0(A_307))
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307)
      | v1_xboole_0('#skF_2'(A_307)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5329])).

tff(c_18,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_189,plain,(
    ! [A_66,A_67] :
      ( ~ v1_xboole_0(u1_struct_0(A_66))
      | ~ r2_hidden(A_67,'#skF_2'(A_66))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_194,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(u1_struct_0(A_66))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66)
      | v1_xboole_0('#skF_2'(A_66)) ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_5351,plain,(
    ! [A_308] :
      ( ~ v3_tex_2('#skF_5',A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308)
      | v1_xboole_0('#skF_2'(A_308)) ) ),
    inference(resolution,[status(thm)],[c_5338,c_194])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_2'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5360,plain,(
    ! [A_309] :
      ( ~ v3_tex_2('#skF_5',A_309)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(resolution,[status(thm)],[c_5351,c_22])).

tff(c_5366,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_5360])).

tff(c_5370,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5366])).

tff(c_5372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:12:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.21/2.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.21/2.79  
% 8.21/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.21/2.79  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 8.21/2.79  
% 8.21/2.79  %Foreground sorts:
% 8.21/2.79  
% 8.21/2.79  
% 8.21/2.79  %Background operators:
% 8.21/2.79  
% 8.21/2.79  
% 8.21/2.79  %Foreground operators:
% 8.21/2.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.21/2.79  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.21/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.21/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.21/2.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.21/2.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.21/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.21/2.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.21/2.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.21/2.79  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.21/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.21/2.79  tff('#skF_5', type, '#skF_5': $i).
% 8.21/2.79  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 8.21/2.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.21/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.21/2.79  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.21/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.21/2.79  tff('#skF_4', type, '#skF_4': $i).
% 8.21/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.21/2.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.21/2.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.21/2.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.21/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.21/2.79  
% 8.21/2.80  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 8.21/2.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.21/2.80  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 8.21/2.80  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.21/2.80  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 8.21/2.80  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 8.21/2.80  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 8.21/2.80  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.21/2.80  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.21/2.80  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.21/2.80  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 8.21/2.80  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.21/2.80  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.21/2.80  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.21/2.80  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.21/2.80  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.21/2.80  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.21/2.80  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.21/2.80  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.21/2.80  tff(c_144, plain, (![A_59]: (m1_subset_1('#skF_2'(A_59), k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.21/2.80  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.21/2.80  tff(c_228, plain, (![A_76, A_77]: (m1_subset_1(A_76, u1_struct_0(A_77)) | ~r2_hidden(A_76, '#skF_2'(A_77)) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_144, c_16])).
% 8.21/2.80  tff(c_233, plain, (![A_77]: (m1_subset_1('#skF_1'('#skF_2'(A_77)), u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77) | v1_xboole_0('#skF_2'(A_77)))), inference(resolution, [status(thm)], [c_4, c_228])).
% 8.21/2.80  tff(c_354, plain, (![A_89]: (m1_subset_1('#skF_1'('#skF_2'(A_89)), u1_struct_0(A_89)) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89) | v1_xboole_0('#skF_2'(A_89)))), inference(resolution, [status(thm)], [c_4, c_228])).
% 8.21/2.80  tff(c_28, plain, (![A_19, B_20]: (k6_domain_1(A_19, B_20)=k1_tarski(B_20) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.21/2.80  tff(c_880, plain, (![A_134]: (k6_domain_1(u1_struct_0(A_134), '#skF_1'('#skF_2'(A_134)))=k1_tarski('#skF_1'('#skF_2'(A_134))) | v1_xboole_0(u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0('#skF_2'(A_134)))), inference(resolution, [status(thm)], [c_354, c_28])).
% 8.21/2.80  tff(c_42, plain, (![A_31, B_33]: (v2_tex_2(k6_domain_1(u1_struct_0(A_31), B_33), A_31) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.21/2.80  tff(c_901, plain, (![A_134]: (v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_134))), A_134) | ~m1_subset_1('#skF_1'('#skF_2'(A_134)), u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0(u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0('#skF_2'(A_134)))), inference(superposition, [status(thm), theory('equality')], [c_880, c_42])).
% 8.21/2.80  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(k6_domain_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.21/2.80  tff(c_3037, plain, (![A_235]: (m1_subset_1(k1_tarski('#skF_1'('#skF_2'(A_235))), k1_zfmisc_1(u1_struct_0(A_235))) | ~m1_subset_1('#skF_1'('#skF_2'(A_235)), u1_struct_0(A_235)) | v1_xboole_0(u1_struct_0(A_235)) | v1_xboole_0(u1_struct_0(A_235)) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235) | v1_xboole_0('#skF_2'(A_235)))), inference(superposition, [status(thm), theory('equality')], [c_880, c_26])).
% 8.21/2.80  tff(c_57, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.21/2.80  tff(c_66, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_57])).
% 8.21/2.80  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.21/2.80  tff(c_76, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_14])).
% 8.21/2.80  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.21/2.80  tff(c_68, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10])).
% 8.21/2.80  tff(c_396, plain, (![C_92, B_93, A_94]: (C_92=B_93 | ~r1_tarski(B_93, C_92) | ~v2_tex_2(C_92, A_94) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_94))) | ~v3_tex_2(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.21/2.80  tff(c_398, plain, (![A_6, A_94]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_94) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_94))) | ~v3_tex_2('#skF_5', A_94) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_68, c_396])).
% 8.21/2.80  tff(c_401, plain, (![A_6, A_94]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_94) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_94))) | ~v3_tex_2('#skF_5', A_94) | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_398])).
% 8.21/2.80  tff(c_5221, plain, (![A_301]: (k1_tarski('#skF_1'('#skF_2'(A_301)))='#skF_5' | ~v2_tex_2(k1_tarski('#skF_1'('#skF_2'(A_301))), A_301) | ~v3_tex_2('#skF_5', A_301) | ~m1_subset_1('#skF_1'('#skF_2'(A_301)), u1_struct_0(A_301)) | v1_xboole_0(u1_struct_0(A_301)) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301) | v1_xboole_0('#skF_2'(A_301)))), inference(resolution, [status(thm)], [c_3037, c_401])).
% 8.21/2.80  tff(c_5226, plain, (![A_302]: (k1_tarski('#skF_1'('#skF_2'(A_302)))='#skF_5' | ~v3_tex_2('#skF_5', A_302) | ~m1_subset_1('#skF_1'('#skF_2'(A_302)), u1_struct_0(A_302)) | v1_xboole_0(u1_struct_0(A_302)) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302) | v1_xboole_0('#skF_2'(A_302)))), inference(resolution, [status(thm)], [c_901, c_5221])).
% 8.21/2.80  tff(c_5307, plain, (![A_306]: (k1_tarski('#skF_1'('#skF_2'(A_306)))='#skF_5' | ~v3_tex_2('#skF_5', A_306) | v1_xboole_0(u1_struct_0(A_306)) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306) | v1_xboole_0('#skF_2'(A_306)))), inference(resolution, [status(thm)], [c_233, c_5226])).
% 8.21/2.80  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.21/2.80  tff(c_5329, plain, (![A_306]: (~v1_xboole_0('#skF_5') | ~v3_tex_2('#skF_5', A_306) | v1_xboole_0(u1_struct_0(A_306)) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306) | v1_xboole_0('#skF_2'(A_306)))), inference(superposition, [status(thm), theory('equality')], [c_5307, c_12])).
% 8.21/2.80  tff(c_5338, plain, (![A_307]: (~v3_tex_2('#skF_5', A_307) | v1_xboole_0(u1_struct_0(A_307)) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | v2_struct_0(A_307) | v1_xboole_0('#skF_2'(A_307)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5329])).
% 8.21/2.80  tff(c_18, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.21/2.80  tff(c_189, plain, (![A_66, A_67]: (~v1_xboole_0(u1_struct_0(A_66)) | ~r2_hidden(A_67, '#skF_2'(A_66)) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_144, c_18])).
% 8.21/2.80  tff(c_194, plain, (![A_66]: (~v1_xboole_0(u1_struct_0(A_66)) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66) | v1_xboole_0('#skF_2'(A_66)))), inference(resolution, [status(thm)], [c_4, c_189])).
% 8.21/2.80  tff(c_5351, plain, (![A_308]: (~v3_tex_2('#skF_5', A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308) | v1_xboole_0('#skF_2'(A_308)))), inference(resolution, [status(thm)], [c_5338, c_194])).
% 8.21/2.80  tff(c_22, plain, (![A_15]: (~v1_xboole_0('#skF_2'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.21/2.80  tff(c_5360, plain, (![A_309]: (~v3_tex_2('#skF_5', A_309) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(resolution, [status(thm)], [c_5351, c_22])).
% 8.21/2.80  tff(c_5366, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_5360])).
% 8.21/2.80  tff(c_5370, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5366])).
% 8.21/2.80  tff(c_5372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5370])).
% 8.21/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.21/2.80  
% 8.21/2.80  Inference rules
% 8.21/2.80  ----------------------
% 8.21/2.80  #Ref     : 0
% 8.21/2.80  #Sup     : 1421
% 8.21/2.80  #Fact    : 2
% 8.21/2.80  #Define  : 0
% 8.21/2.80  #Split   : 3
% 8.21/2.80  #Chain   : 0
% 8.21/2.80  #Close   : 0
% 8.21/2.80  
% 8.21/2.80  Ordering : KBO
% 8.21/2.80  
% 8.21/2.80  Simplification rules
% 8.21/2.80  ----------------------
% 8.21/2.80  #Subsume      : 275
% 8.21/2.80  #Demod        : 484
% 8.21/2.80  #Tautology    : 343
% 8.21/2.80  #SimpNegUnit  : 34
% 8.21/2.80  #BackRed      : 10
% 8.21/2.80  
% 8.21/2.80  #Partial instantiations: 0
% 8.21/2.80  #Strategies tried      : 1
% 8.21/2.80  
% 8.21/2.80  Timing (in seconds)
% 8.21/2.80  ----------------------
% 8.21/2.80  Preprocessing        : 0.36
% 8.21/2.80  Parsing              : 0.18
% 8.21/2.80  CNF conversion       : 0.03
% 8.21/2.80  Main loop            : 1.65
% 8.21/2.81  Inferencing          : 0.50
% 8.21/2.81  Reduction            : 0.47
% 8.21/2.81  Demodulation         : 0.30
% 8.21/2.81  BG Simplification    : 0.07
% 8.21/2.81  Subsumption          : 0.51
% 8.21/2.81  Abstraction          : 0.09
% 8.21/2.81  MUC search           : 0.00
% 8.21/2.81  Cooper               : 0.00
% 8.21/2.81  Total                : 2.05
% 8.21/2.81  Index Insertion      : 0.00
% 8.21/2.81  Index Deletion       : 0.00
% 8.21/2.81  Index Matching       : 0.00
% 8.21/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
