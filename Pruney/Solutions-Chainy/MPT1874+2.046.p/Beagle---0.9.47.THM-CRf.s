%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 215 expanded)
%              Number of leaves         :   33 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 ( 531 expanded)
%              Number of equality atoms :   18 ( 107 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_84,axiom,(
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

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_81,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k1_tarski(A_36),k1_zfmisc_1(B_37))
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_81,c_6])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_62,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_34,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_65,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_87,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,
    ( k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_65,c_87])).

tff(c_104,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_14])).

tff(c_110,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_107])).

tff(c_122,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_122])).

tff(c_128,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_127,plain,(
    k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_134,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k6_domain_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_143,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_134])).

tff(c_147,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_143])).

tff(c_148,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_147])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_502,plain,(
    ! [A_92,B_93,C_94] :
      ( k9_subset_1(u1_struct_0(A_92),B_93,k2_pre_topc(A_92,C_94)) = C_94
      | ~ r1_tarski(C_94,B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_515,plain,(
    ! [B_93,C_94] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_93,k2_pre_topc('#skF_2',C_94)) = C_94
      | ~ r1_tarski(C_94,B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v2_tex_2(B_93,'#skF_2')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_502])).

tff(c_521,plain,(
    ! [B_93,C_94] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_93,k2_pre_topc('#skF_2',C_94)) = C_94
      | ~ r1_tarski(C_94,B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v2_tex_2(B_93,'#skF_2')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_62,c_62,c_515])).

tff(c_523,plain,(
    ! [B_95,C_96] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_95,k2_pre_topc('#skF_2',C_96)) = C_96
      | ~ r1_tarski(C_96,B_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v2_tex_2(B_95,'#skF_2')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_521])).

tff(c_582,plain,(
    ! [B_98] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_98,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_98)
      | ~ v2_tex_2(B_98,'#skF_2')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_148,c_523])).

tff(c_28,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_63,plain,(
    k9_subset_1(k2_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_62,c_28])).

tff(c_129,plain,(
    k9_subset_1(k2_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_127,c_63])).

tff(c_588,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_129])).

tff(c_595,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34,c_588])).

tff(c_599,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_595])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.83/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.44  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.83/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.44  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.83/1.44  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.83/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.44  
% 2.83/1.45  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.83/1.45  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.83/1.45  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.83/1.45  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.83/1.45  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.83/1.45  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.83/1.45  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.83/1.45  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.83/1.45  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.83/1.45  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_81, plain, (![A_36, B_37]: (m1_subset_1(k1_tarski(A_36), k1_zfmisc_1(B_37)) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.45  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.45  tff(c_85, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(resolution, [status(thm)], [c_81, c_6])).
% 2.83/1.45  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.45  tff(c_53, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.45  tff(c_58, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_12, c_53])).
% 2.83/1.45  tff(c_62, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.83/1.45  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 2.83/1.45  tff(c_34, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_65, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 2.83/1.45  tff(c_87, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.45  tff(c_103, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_65, c_87])).
% 2.83/1.45  tff(c_104, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_103])).
% 2.83/1.45  tff(c_14, plain, (![A_8]: (~v1_xboole_0(k2_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.45  tff(c_107, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_104, c_14])).
% 2.83/1.45  tff(c_110, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_107])).
% 2.83/1.45  tff(c_122, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_110])).
% 2.83/1.45  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_122])).
% 2.83/1.45  tff(c_128, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_103])).
% 2.83/1.45  tff(c_127, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_103])).
% 2.83/1.45  tff(c_134, plain, (![A_44, B_45]: (m1_subset_1(k6_domain_1(A_44, B_45), k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.45  tff(c_143, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_134])).
% 2.83/1.45  tff(c_147, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_143])).
% 2.83/1.45  tff(c_148, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_128, c_147])).
% 2.83/1.45  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_502, plain, (![A_92, B_93, C_94]: (k9_subset_1(u1_struct_0(A_92), B_93, k2_pre_topc(A_92, C_94))=C_94 | ~r1_tarski(C_94, B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.45  tff(c_515, plain, (![B_93, C_94]: (k9_subset_1(u1_struct_0('#skF_2'), B_93, k2_pre_topc('#skF_2', C_94))=C_94 | ~r1_tarski(C_94, B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v2_tex_2(B_93, '#skF_2') | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_502])).
% 2.83/1.45  tff(c_521, plain, (![B_93, C_94]: (k9_subset_1(k2_struct_0('#skF_2'), B_93, k2_pre_topc('#skF_2', C_94))=C_94 | ~r1_tarski(C_94, B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v2_tex_2(B_93, '#skF_2') | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_62, c_62, c_515])).
% 2.83/1.45  tff(c_523, plain, (![B_95, C_96]: (k9_subset_1(k2_struct_0('#skF_2'), B_95, k2_pre_topc('#skF_2', C_96))=C_96 | ~r1_tarski(C_96, B_95) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v2_tex_2(B_95, '#skF_2') | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_521])).
% 2.83/1.45  tff(c_582, plain, (![B_98]: (k9_subset_1(k2_struct_0('#skF_2'), B_98, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_98) | ~v2_tex_2(B_98, '#skF_2') | ~m1_subset_1(B_98, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_148, c_523])).
% 2.83/1.45  tff(c_28, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_63, plain, (k9_subset_1(k2_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_62, c_28])).
% 2.83/1.45  tff(c_129, plain, (k9_subset_1(k2_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_127, c_63])).
% 2.83/1.45  tff(c_588, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_582, c_129])).
% 2.83/1.45  tff(c_595, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34, c_588])).
% 2.83/1.45  tff(c_599, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_85, c_595])).
% 2.83/1.45  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_599])).
% 2.83/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  Inference rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Ref     : 0
% 2.83/1.45  #Sup     : 125
% 2.83/1.45  #Fact    : 0
% 2.83/1.45  #Define  : 0
% 2.83/1.45  #Split   : 4
% 2.83/1.45  #Chain   : 0
% 2.83/1.45  #Close   : 0
% 2.83/1.45  
% 2.83/1.45  Ordering : KBO
% 2.83/1.45  
% 2.83/1.45  Simplification rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Subsume      : 4
% 2.83/1.45  #Demod        : 55
% 2.83/1.45  #Tautology    : 42
% 2.83/1.45  #SimpNegUnit  : 14
% 2.83/1.45  #BackRed      : 4
% 2.83/1.45  
% 2.83/1.45  #Partial instantiations: 0
% 2.83/1.45  #Strategies tried      : 1
% 2.83/1.45  
% 2.83/1.45  Timing (in seconds)
% 2.83/1.45  ----------------------
% 2.83/1.45  Preprocessing        : 0.31
% 2.83/1.45  Parsing              : 0.17
% 2.83/1.45  CNF conversion       : 0.02
% 2.83/1.45  Main loop            : 0.35
% 2.83/1.45  Inferencing          : 0.14
% 2.83/1.45  Reduction            : 0.10
% 2.83/1.45  Demodulation         : 0.07
% 2.83/1.45  BG Simplification    : 0.02
% 2.83/1.45  Subsumption          : 0.07
% 2.83/1.45  Abstraction          : 0.02
% 2.83/1.45  MUC search           : 0.00
% 2.83/1.45  Cooper               : 0.00
% 2.83/1.46  Total                : 0.70
% 2.83/1.46  Index Insertion      : 0.00
% 2.83/1.46  Index Deletion       : 0.00
% 2.83/1.46  Index Matching       : 0.00
% 2.83/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
