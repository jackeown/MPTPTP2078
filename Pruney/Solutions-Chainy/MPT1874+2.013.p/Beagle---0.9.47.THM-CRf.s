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
% DateTime   : Thu Dec  3 10:29:38 EST 2020

% Result     : Theorem 4.30s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 167 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 460 expanded)
%              Number of equality atoms :   13 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_110,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k1_tarski(A_74),k1_zfmisc_1(B_75))
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_118,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tarski(A_74),B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_110,c_26])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_157,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_173,plain,(
    ! [A_90] :
      ( r2_hidden('#skF_5',A_90)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_90)) ) ),
    inference(resolution,[status(thm)],[c_42,c_157])).

tff(c_182,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_173])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_883,plain,(
    ! [A_221,B_222,C_223] :
      ( k9_subset_1(u1_struct_0(A_221),B_222,k2_pre_topc(A_221,C_223)) = C_223
      | ~ r1_tarski(C_223,B_222)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ v2_tex_2(B_222,A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1267,plain,(
    ! [A_299,B_300,A_301] :
      ( k9_subset_1(u1_struct_0(A_299),B_300,k2_pre_topc(A_299,A_301)) = A_301
      | ~ r1_tarski(A_301,B_300)
      | ~ v2_tex_2(B_300,A_299)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299)
      | ~ r1_tarski(A_301,u1_struct_0(A_299)) ) ),
    inference(resolution,[status(thm)],[c_28,c_883])).

tff(c_1277,plain,(
    ! [A_301] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_301)) = A_301
      | ~ r1_tarski(A_301,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_301,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1267])).

tff(c_1283,plain,(
    ! [A_301] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_301)) = A_301
      | ~ r1_tarski(A_301,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_301,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_1277])).

tff(c_1285,plain,(
    ! [A_302] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_302)) = A_302
      | ~ r1_tarski(A_302,'#skF_4')
      | ~ r1_tarski(A_302,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1283])).

tff(c_55,plain,(
    ! [B_60,A_61] :
      ( ~ r2_hidden(B_60,A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_55])).

tff(c_93,plain,(
    ! [B_70,A_71] :
      ( v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_103,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_99])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_133,plain,(
    ! [A_81,B_82] :
      ( k6_domain_1(A_81,B_82) = k1_tarski(B_82)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_145,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_133])).

tff(c_151,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_145])).

tff(c_40,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_152,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_151,c_40])).

tff(c_1314,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_152])).

tff(c_1318,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_1321,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_118,c_1318])).

tff(c_1325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_1321])).

tff(c_1326,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_1330,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_1326])).

tff(c_1334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.30/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.74  
% 4.30/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.74  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.30/1.74  
% 4.30/1.74  %Foreground sorts:
% 4.30/1.74  
% 4.30/1.74  
% 4.30/1.74  %Background operators:
% 4.30/1.74  
% 4.30/1.74  
% 4.30/1.74  %Foreground operators:
% 4.30/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.30/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.30/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.30/1.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.30/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.30/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.30/1.74  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.30/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.30/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.30/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.30/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.30/1.74  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.30/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.30/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.30/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.30/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.30/1.74  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.30/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.30/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.30/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.30/1.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.30/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.30/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.30/1.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.30/1.74  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.30/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.30/1.74  
% 4.30/1.76  tff(f_113, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.30/1.76  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.30/1.76  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.30/1.76  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.30/1.76  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.30/1.76  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.30/1.76  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.30/1.76  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.30/1.76  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_110, plain, (![A_74, B_75]: (m1_subset_1(k1_tarski(A_74), k1_zfmisc_1(B_75)) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.30/1.76  tff(c_26, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.30/1.76  tff(c_118, plain, (![A_74, B_75]: (r1_tarski(k1_tarski(A_74), B_75) | ~r2_hidden(A_74, B_75))), inference(resolution, [status(thm)], [c_110, c_26])).
% 4.30/1.76  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_157, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.30/1.76  tff(c_173, plain, (![A_90]: (r2_hidden('#skF_5', A_90) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_90)))), inference(resolution, [status(thm)], [c_42, c_157])).
% 4.30/1.76  tff(c_182, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_173])).
% 4.30/1.76  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_46, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_28, plain, (![A_42, B_43]: (m1_subset_1(A_42, k1_zfmisc_1(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.30/1.76  tff(c_883, plain, (![A_221, B_222, C_223]: (k9_subset_1(u1_struct_0(A_221), B_222, k2_pre_topc(A_221, C_223))=C_223 | ~r1_tarski(C_223, B_222) | ~m1_subset_1(C_223, k1_zfmisc_1(u1_struct_0(A_221))) | ~v2_tex_2(B_222, A_221) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.30/1.76  tff(c_1267, plain, (![A_299, B_300, A_301]: (k9_subset_1(u1_struct_0(A_299), B_300, k2_pre_topc(A_299, A_301))=A_301 | ~r1_tarski(A_301, B_300) | ~v2_tex_2(B_300, A_299) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299) | ~r1_tarski(A_301, u1_struct_0(A_299)))), inference(resolution, [status(thm)], [c_28, c_883])).
% 4.30/1.76  tff(c_1277, plain, (![A_301]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_301))=A_301 | ~r1_tarski(A_301, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_301, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_1267])).
% 4.30/1.76  tff(c_1283, plain, (![A_301]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_301))=A_301 | ~r1_tarski(A_301, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_301, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_1277])).
% 4.30/1.76  tff(c_1285, plain, (![A_302]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_302))=A_302 | ~r1_tarski(A_302, '#skF_4') | ~r1_tarski(A_302, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1283])).
% 4.30/1.76  tff(c_55, plain, (![B_60, A_61]: (~r2_hidden(B_60, A_61) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.76  tff(c_59, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_55])).
% 4.30/1.76  tff(c_93, plain, (![B_70, A_71]: (v1_xboole_0(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.30/1.76  tff(c_99, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_93])).
% 4.30/1.76  tff(c_103, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_59, c_99])).
% 4.30/1.76  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_133, plain, (![A_81, B_82]: (k6_domain_1(A_81, B_82)=k1_tarski(B_82) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.30/1.76  tff(c_145, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_133])).
% 4.30/1.76  tff(c_151, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_103, c_145])).
% 4.30/1.76  tff(c_40, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.30/1.76  tff(c_152, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_151, c_40])).
% 4.30/1.76  tff(c_1314, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1285, c_152])).
% 4.30/1.76  tff(c_1318, plain, (~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1314])).
% 4.30/1.76  tff(c_1321, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_118, c_1318])).
% 4.30/1.76  tff(c_1325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_1321])).
% 4.30/1.76  tff(c_1326, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1314])).
% 4.30/1.76  tff(c_1330, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_118, c_1326])).
% 4.30/1.76  tff(c_1334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1330])).
% 4.30/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.76  
% 4.30/1.76  Inference rules
% 4.30/1.76  ----------------------
% 4.30/1.76  #Ref     : 0
% 4.30/1.76  #Sup     : 301
% 4.30/1.76  #Fact    : 0
% 4.30/1.76  #Define  : 0
% 4.30/1.76  #Split   : 7
% 4.30/1.76  #Chain   : 0
% 4.30/1.76  #Close   : 0
% 4.30/1.76  
% 4.30/1.76  Ordering : KBO
% 4.30/1.76  
% 4.30/1.76  Simplification rules
% 4.30/1.76  ----------------------
% 4.30/1.76  #Subsume      : 48
% 4.30/1.76  #Demod        : 39
% 4.30/1.76  #Tautology    : 44
% 4.30/1.76  #SimpNegUnit  : 12
% 4.30/1.76  #BackRed      : 1
% 4.30/1.76  
% 4.30/1.76  #Partial instantiations: 0
% 4.30/1.76  #Strategies tried      : 1
% 4.30/1.76  
% 4.30/1.76  Timing (in seconds)
% 4.30/1.76  ----------------------
% 4.30/1.76  Preprocessing        : 0.34
% 4.30/1.76  Parsing              : 0.18
% 4.30/1.76  CNF conversion       : 0.02
% 4.30/1.76  Main loop            : 0.66
% 4.30/1.76  Inferencing          : 0.21
% 4.30/1.76  Reduction            : 0.15
% 4.30/1.76  Demodulation         : 0.09
% 4.30/1.76  BG Simplification    : 0.03
% 4.30/1.76  Subsumption          : 0.23
% 4.30/1.76  Abstraction          : 0.03
% 4.30/1.76  MUC search           : 0.00
% 4.30/1.76  Cooper               : 0.00
% 4.30/1.76  Total                : 1.02
% 4.30/1.76  Index Insertion      : 0.00
% 4.30/1.76  Index Deletion       : 0.00
% 4.30/1.76  Index Matching       : 0.00
% 4.30/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
