%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:21 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 294 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_75,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k1_tarski(A_57),k1_zfmisc_1(B_58))
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_tarski(A_57),B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_75,c_10])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_46])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    ! [C_61,A_62,B_63] :
      ( r2_hidden(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [A_64] :
      ( r2_hidden('#skF_5',A_64)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_28,c_86])).

tff(c_98,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_5',B_11)
      | ~ r1_tarski('#skF_4',B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_216,plain,(
    ! [A_92,B_93,C_94] :
      ( v4_pre_topc('#skF_1'(A_92,B_93,C_94),A_92)
      | ~ r1_tarski(C_94,B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_284,plain,(
    ! [A_100,B_101,A_102] :
      ( v4_pre_topc('#skF_1'(A_100,B_101,A_102),A_100)
      | ~ r1_tarski(A_102,B_101)
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ r1_tarski(A_102,u1_struct_0(A_100)) ) ),
    inference(resolution,[status(thm)],[c_12,c_216])).

tff(c_297,plain,(
    ! [A_100,A_10,A_102] :
      ( v4_pre_topc('#skF_1'(A_100,A_10,A_102),A_100)
      | ~ r1_tarski(A_102,A_10)
      | ~ v2_tex_2(A_10,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ r1_tarski(A_102,u1_struct_0(A_100))
      | ~ r1_tarski(A_10,u1_struct_0(A_100)) ) ),
    inference(resolution,[status(thm)],[c_12,c_284])).

tff(c_360,plain,(
    ! [A_126,B_127,C_128] :
      ( k9_subset_1(u1_struct_0(A_126),B_127,'#skF_1'(A_126,B_127,C_128)) = C_128
      | ~ r1_tarski(C_128,B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ v2_tex_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_446,plain,(
    ! [A_134,B_135,A_136] :
      ( k9_subset_1(u1_struct_0(A_134),B_135,'#skF_1'(A_134,B_135,A_136)) = A_136
      | ~ r1_tarski(A_136,B_135)
      | ~ v2_tex_2(B_135,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ r1_tarski(A_136,u1_struct_0(A_134)) ) ),
    inference(resolution,[status(thm)],[c_12,c_360])).

tff(c_458,plain,(
    ! [A_136] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_136)) = A_136
      | ~ r1_tarski(A_136,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_136,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_446])).

tff(c_466,plain,(
    ! [A_137] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_137)) = A_137
      | ~ r1_tarski(A_137,'#skF_4')
      | ~ r1_tarski(A_137,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_458])).

tff(c_309,plain,(
    ! [A_120,B_121,C_122] :
      ( m1_subset_1('#skF_1'(A_120,B_121,C_122),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ r1_tarski(C_122,B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v2_tex_2(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [D_48] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_48) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_48,'#skF_3')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_333,plain,(
    ! [B_121,C_122] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_121,C_122)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_121,C_122),'#skF_3')
      | ~ r1_tarski(C_122,B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_309,c_26])).

tff(c_350,plain,(
    ! [B_121,C_122] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_121,C_122)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_121,C_122),'#skF_3')
      | ~ r1_tarski(C_122,B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_333])).

tff(c_471,plain,(
    ! [A_137] :
      ( k1_tarski('#skF_5') != A_137
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_137),'#skF_3')
      | ~ r1_tarski(A_137,'#skF_4')
      | ~ m1_subset_1(A_137,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_137,'#skF_4')
      | ~ r1_tarski(A_137,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_350])).

tff(c_496,plain,(
    ! [A_138] :
      ( k1_tarski('#skF_5') != A_138
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_138),'#skF_3')
      | ~ m1_subset_1(A_138,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_138,'#skF_4')
      | ~ r1_tarski(A_138,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_471])).

tff(c_528,plain,(
    ! [A_139] :
      ( k1_tarski('#skF_5') != A_139
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_139),'#skF_3')
      | ~ r1_tarski(A_139,'#skF_4')
      | ~ r1_tarski(A_139,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_496])).

tff(c_536,plain,(
    ! [A_102] :
      ( k1_tarski('#skF_5') != A_102
      | ~ r1_tarski(A_102,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_102,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_297,c_528])).

tff(c_555,plain,(
    ! [A_140] :
      ( k1_tarski('#skF_5') != A_140
      | ~ r1_tarski(A_140,'#skF_4')
      | ~ r1_tarski(A_140,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_32,c_536])).

tff(c_614,plain,(
    ! [A_144] :
      ( k1_tarski(A_144) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_144),'#skF_4')
      | ~ r2_hidden(A_144,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_84,c_555])).

tff(c_618,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_614])).

tff(c_624,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_618])).

tff(c_628,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_624])).

tff(c_632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:45:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.43  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.74/1.43  
% 2.74/1.43  %Foreground sorts:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Background operators:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Foreground operators:
% 2.74/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.74/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.74/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.43  
% 3.06/1.44  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 3.06/1.44  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.06/1.44  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.44  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.06/1.44  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 3.06/1.44  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.44  tff(c_75, plain, (![A_57, B_58]: (m1_subset_1(k1_tarski(A_57), k1_zfmisc_1(B_58)) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.06/1.44  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.06/1.44  tff(c_84, plain, (![A_57, B_58]: (r1_tarski(k1_tarski(A_57), B_58) | ~r2_hidden(A_57, B_58))), inference(resolution, [status(thm)], [c_75, c_10])).
% 3.06/1.44  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.44  tff(c_46, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.06/1.44  tff(c_50, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_46])).
% 3.06/1.44  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.06/1.44  tff(c_86, plain, (![C_61, A_62, B_63]: (r2_hidden(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.06/1.44  tff(c_90, plain, (![A_64]: (r2_hidden('#skF_5', A_64) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_64)))), inference(resolution, [status(thm)], [c_28, c_86])).
% 3.06/1.44  tff(c_98, plain, (![B_11]: (r2_hidden('#skF_5', B_11) | ~r1_tarski('#skF_4', B_11))), inference(resolution, [status(thm)], [c_12, c_90])).
% 3.06/1.44  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.44  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.44  tff(c_216, plain, (![A_92, B_93, C_94]: (v4_pre_topc('#skF_1'(A_92, B_93, C_94), A_92) | ~r1_tarski(C_94, B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.44  tff(c_284, plain, (![A_100, B_101, A_102]: (v4_pre_topc('#skF_1'(A_100, B_101, A_102), A_100) | ~r1_tarski(A_102, B_101) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~r1_tarski(A_102, u1_struct_0(A_100)))), inference(resolution, [status(thm)], [c_12, c_216])).
% 3.06/1.44  tff(c_297, plain, (![A_100, A_10, A_102]: (v4_pre_topc('#skF_1'(A_100, A_10, A_102), A_100) | ~r1_tarski(A_102, A_10) | ~v2_tex_2(A_10, A_100) | ~l1_pre_topc(A_100) | ~r1_tarski(A_102, u1_struct_0(A_100)) | ~r1_tarski(A_10, u1_struct_0(A_100)))), inference(resolution, [status(thm)], [c_12, c_284])).
% 3.06/1.44  tff(c_360, plain, (![A_126, B_127, C_128]: (k9_subset_1(u1_struct_0(A_126), B_127, '#skF_1'(A_126, B_127, C_128))=C_128 | ~r1_tarski(C_128, B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_126))) | ~v2_tex_2(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.44  tff(c_446, plain, (![A_134, B_135, A_136]: (k9_subset_1(u1_struct_0(A_134), B_135, '#skF_1'(A_134, B_135, A_136))=A_136 | ~r1_tarski(A_136, B_135) | ~v2_tex_2(B_135, A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~r1_tarski(A_136, u1_struct_0(A_134)))), inference(resolution, [status(thm)], [c_12, c_360])).
% 3.06/1.44  tff(c_458, plain, (![A_136]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_136))=A_136 | ~r1_tarski(A_136, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_136, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_446])).
% 3.06/1.44  tff(c_466, plain, (![A_137]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', A_137))=A_137 | ~r1_tarski(A_137, '#skF_4') | ~r1_tarski(A_137, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_458])).
% 3.06/1.44  tff(c_309, plain, (![A_120, B_121, C_122]: (m1_subset_1('#skF_1'(A_120, B_121, C_122), k1_zfmisc_1(u1_struct_0(A_120))) | ~r1_tarski(C_122, B_121) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(A_120))) | ~v2_tex_2(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.44  tff(c_26, plain, (![D_48]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_48)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_48, '#skF_3') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.44  tff(c_333, plain, (![B_121, C_122]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_121, C_122))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_121, C_122), '#skF_3') | ~r1_tarski(C_122, B_121) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_121, '#skF_3') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_309, c_26])).
% 3.06/1.44  tff(c_350, plain, (![B_121, C_122]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_121, C_122))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_121, C_122), '#skF_3') | ~r1_tarski(C_122, B_121) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_121, '#skF_3') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_333])).
% 3.06/1.44  tff(c_471, plain, (![A_137]: (k1_tarski('#skF_5')!=A_137 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_137), '#skF_3') | ~r1_tarski(A_137, '#skF_4') | ~m1_subset_1(A_137, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_137, '#skF_4') | ~r1_tarski(A_137, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_466, c_350])).
% 3.06/1.44  tff(c_496, plain, (![A_138]: (k1_tarski('#skF_5')!=A_138 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_138), '#skF_3') | ~m1_subset_1(A_138, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_138, '#skF_4') | ~r1_tarski(A_138, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_471])).
% 3.06/1.44  tff(c_528, plain, (![A_139]: (k1_tarski('#skF_5')!=A_139 | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', A_139), '#skF_3') | ~r1_tarski(A_139, '#skF_4') | ~r1_tarski(A_139, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_496])).
% 3.06/1.44  tff(c_536, plain, (![A_102]: (k1_tarski('#skF_5')!=A_102 | ~r1_tarski(A_102, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_102, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_297, c_528])).
% 3.06/1.44  tff(c_555, plain, (![A_140]: (k1_tarski('#skF_5')!=A_140 | ~r1_tarski(A_140, '#skF_4') | ~r1_tarski(A_140, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_32, c_536])).
% 3.06/1.44  tff(c_614, plain, (![A_144]: (k1_tarski(A_144)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_144), '#skF_4') | ~r2_hidden(A_144, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_84, c_555])).
% 3.06/1.44  tff(c_618, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_614])).
% 3.06/1.44  tff(c_624, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_618])).
% 3.06/1.44  tff(c_628, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_624])).
% 3.06/1.44  tff(c_632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_628])).
% 3.06/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.44  
% 3.06/1.44  Inference rules
% 3.06/1.44  ----------------------
% 3.06/1.44  #Ref     : 0
% 3.06/1.44  #Sup     : 114
% 3.06/1.44  #Fact    : 0
% 3.06/1.44  #Define  : 0
% 3.06/1.44  #Split   : 2
% 3.06/1.44  #Chain   : 0
% 3.06/1.44  #Close   : 0
% 3.06/1.44  
% 3.06/1.44  Ordering : KBO
% 3.06/1.44  
% 3.06/1.44  Simplification rules
% 3.06/1.44  ----------------------
% 3.06/1.44  #Subsume      : 14
% 3.06/1.44  #Demod        : 69
% 3.06/1.44  #Tautology    : 25
% 3.06/1.44  #SimpNegUnit  : 0
% 3.06/1.44  #BackRed      : 0
% 3.06/1.44  
% 3.06/1.44  #Partial instantiations: 0
% 3.06/1.44  #Strategies tried      : 1
% 3.06/1.44  
% 3.06/1.44  Timing (in seconds)
% 3.06/1.44  ----------------------
% 3.06/1.45  Preprocessing        : 0.32
% 3.06/1.45  Parsing              : 0.17
% 3.06/1.45  CNF conversion       : 0.03
% 3.06/1.45  Main loop            : 0.37
% 3.06/1.45  Inferencing          : 0.15
% 3.06/1.45  Reduction            : 0.09
% 3.06/1.45  Demodulation         : 0.07
% 3.06/1.45  BG Simplification    : 0.02
% 3.06/1.45  Subsumption          : 0.08
% 3.06/1.45  Abstraction          : 0.02
% 3.06/1.45  MUC search           : 0.00
% 3.06/1.45  Cooper               : 0.00
% 3.06/1.45  Total                : 0.72
% 3.06/1.45  Index Insertion      : 0.00
% 3.06/1.45  Index Deletion       : 0.00
% 3.06/1.45  Index Matching       : 0.00
% 3.06/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
