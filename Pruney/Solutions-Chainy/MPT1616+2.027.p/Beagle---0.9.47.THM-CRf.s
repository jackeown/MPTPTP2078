%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:38 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 144 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 361 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_131,plain,(
    ! [A_53] :
      ( m1_subset_1(u1_pre_topc(A_53),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [A_53] :
      ( r1_tarski(u1_pre_topc(A_53),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_131,c_12])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_14] :
      ( r2_hidden(u1_struct_0(A_14),u1_pre_topc(A_14))
      | ~ v2_pre_topc(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_143,plain,(
    ! [C_55,B_56,A_57] :
      ( r1_tarski(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(k3_tarski(A_57),B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_301,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(u1_struct_0(A_85),B_86)
      | ~ r1_tarski(k3_tarski(u1_pre_topc(A_85)),B_86)
      | ~ v2_pre_topc(A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_54,c_143])).

tff(c_317,plain,(
    ! [A_87] :
      ( r1_tarski(u1_struct_0(A_87),k3_tarski(u1_pre_topc(A_87)))
      | ~ v2_pre_topc(A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_301])).

tff(c_10,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k3_tarski(A_36),k3_tarski(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_40,A_41] :
      ( r1_tarski(k3_tarski(A_40),A_41)
      | ~ r1_tarski(A_40,k1_zfmisc_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_40,A_41] :
      ( k3_tarski(A_40) = A_41
      | ~ r1_tarski(A_41,k3_tarski(A_40))
      | ~ r1_tarski(A_40,k1_zfmisc_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_546,plain,(
    ! [A_122] :
      ( k3_tarski(u1_pre_topc(A_122)) = u1_struct_0(A_122)
      | ~ r1_tarski(u1_pre_topc(A_122),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ v2_pre_topc(A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_317,c_107])).

tff(c_550,plain,(
    ! [A_53] :
      ( k3_tarski(u1_pre_topc(A_53)) = u1_struct_0(A_53)
      | ~ v2_pre_topc(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_138,c_546])).

tff(c_551,plain,(
    ! [A_123] :
      ( k3_tarski(u1_pre_topc(A_123)) = u1_struct_0(A_123)
      | ~ v2_pre_topc(A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_138,c_546])).

tff(c_58,plain,(
    ! [A_29] :
      ( k4_yellow_0(k2_yellow_1(A_29)) = k3_tarski(A_29)
      | ~ r2_hidden(k3_tarski(A_29),A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1830,plain,(
    ! [A_261] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_261))) = k3_tarski(u1_pre_topc(A_261))
      | ~ r2_hidden(u1_struct_0(A_261),u1_pre_topc(A_261))
      | v1_xboole_0(u1_pre_topc(A_261))
      | ~ v2_pre_topc(A_261)
      | ~ l1_pre_topc(A_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_58])).

tff(c_1835,plain,(
    ! [A_262] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_262))) = k3_tarski(u1_pre_topc(A_262))
      | v1_xboole_0(u1_pre_topc(A_262))
      | ~ v2_pre_topc(A_262)
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_54,c_1830])).

tff(c_60,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1841,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1835,c_60])).

tff(c_1847,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_1841])).

tff(c_1849,plain,(
    k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1847])).

tff(c_1852,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_1849])).

tff(c_1856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_1852])).

tff(c_1857,plain,(
    v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1847])).

tff(c_127,plain,(
    ! [A_52] :
      ( r2_hidden(u1_struct_0(A_52),u1_pre_topc(A_52))
      | ~ v2_pre_topc(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [C_46,B_47,A_48] :
      ( ~ v1_xboole_0(C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_125,plain,(
    ! [B_7,A_48,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_48,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_122])).

tff(c_153,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | ~ r1_tarski(u1_pre_topc(A_62),B_61)
      | ~ v2_pre_topc(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_127,c_125])).

tff(c_162,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(u1_pre_topc(A_62))
      | ~ v2_pre_topc(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_1861,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1857,c_162])).

tff(c_1865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_1861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:02:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.25/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.04  
% 5.25/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.05  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 5.25/2.05  
% 5.25/2.05  %Foreground sorts:
% 5.25/2.05  
% 5.25/2.05  
% 5.25/2.05  %Background operators:
% 5.25/2.05  
% 5.25/2.05  
% 5.25/2.05  %Foreground operators:
% 5.25/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.25/2.05  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.25/2.05  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.25/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.25/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.25/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.25/2.05  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 5.25/2.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.25/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.25/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.25/2.05  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 5.25/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.25/2.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.25/2.05  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 5.25/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.25/2.05  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.25/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.25/2.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.25/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.25/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.25/2.05  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.25/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.25/2.05  
% 5.25/2.06  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 5.25/2.06  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.25/2.06  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.25/2.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.25/2.06  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 5.25/2.06  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 5.25/2.06  tff(f_37, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.25/2.06  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 5.25/2.06  tff(f_90, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 5.25/2.06  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.25/2.06  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.25/2.06  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.25/2.06  tff(c_131, plain, (![A_53]: (m1_subset_1(u1_pre_topc(A_53), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.25/2.06  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.25/2.06  tff(c_138, plain, (![A_53]: (r1_tarski(u1_pre_topc(A_53), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_131, c_12])).
% 5.25/2.06  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.25/2.06  tff(c_54, plain, (![A_14]: (r2_hidden(u1_struct_0(A_14), u1_pre_topc(A_14)) | ~v2_pre_topc(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.25/2.06  tff(c_143, plain, (![C_55, B_56, A_57]: (r1_tarski(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(k3_tarski(A_57), B_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.25/2.06  tff(c_301, plain, (![A_85, B_86]: (r1_tarski(u1_struct_0(A_85), B_86) | ~r1_tarski(k3_tarski(u1_pre_topc(A_85)), B_86) | ~v2_pre_topc(A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_54, c_143])).
% 5.25/2.06  tff(c_317, plain, (![A_87]: (r1_tarski(u1_struct_0(A_87), k3_tarski(u1_pre_topc(A_87))) | ~v2_pre_topc(A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_6, c_301])).
% 5.25/2.06  tff(c_10, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.25/2.06  tff(c_84, plain, (![A_36, B_37]: (r1_tarski(k3_tarski(A_36), k3_tarski(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.25/2.06  tff(c_101, plain, (![A_40, A_41]: (r1_tarski(k3_tarski(A_40), A_41) | ~r1_tarski(A_40, k1_zfmisc_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_84])).
% 5.25/2.06  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.25/2.06  tff(c_107, plain, (![A_40, A_41]: (k3_tarski(A_40)=A_41 | ~r1_tarski(A_41, k3_tarski(A_40)) | ~r1_tarski(A_40, k1_zfmisc_1(A_41)))), inference(resolution, [status(thm)], [c_101, c_2])).
% 5.25/2.06  tff(c_546, plain, (![A_122]: (k3_tarski(u1_pre_topc(A_122))=u1_struct_0(A_122) | ~r1_tarski(u1_pre_topc(A_122), k1_zfmisc_1(u1_struct_0(A_122))) | ~v2_pre_topc(A_122) | ~l1_pre_topc(A_122))), inference(resolution, [status(thm)], [c_317, c_107])).
% 5.25/2.06  tff(c_550, plain, (![A_53]: (k3_tarski(u1_pre_topc(A_53))=u1_struct_0(A_53) | ~v2_pre_topc(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_138, c_546])).
% 5.25/2.06  tff(c_551, plain, (![A_123]: (k3_tarski(u1_pre_topc(A_123))=u1_struct_0(A_123) | ~v2_pre_topc(A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_138, c_546])).
% 5.25/2.06  tff(c_58, plain, (![A_29]: (k4_yellow_0(k2_yellow_1(A_29))=k3_tarski(A_29) | ~r2_hidden(k3_tarski(A_29), A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.25/2.06  tff(c_1830, plain, (![A_261]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_261)))=k3_tarski(u1_pre_topc(A_261)) | ~r2_hidden(u1_struct_0(A_261), u1_pre_topc(A_261)) | v1_xboole_0(u1_pre_topc(A_261)) | ~v2_pre_topc(A_261) | ~l1_pre_topc(A_261))), inference(superposition, [status(thm), theory('equality')], [c_551, c_58])).
% 5.25/2.06  tff(c_1835, plain, (![A_262]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_262)))=k3_tarski(u1_pre_topc(A_262)) | v1_xboole_0(u1_pre_topc(A_262)) | ~v2_pre_topc(A_262) | ~l1_pre_topc(A_262))), inference(resolution, [status(thm)], [c_54, c_1830])).
% 5.25/2.06  tff(c_60, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4')))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.25/2.06  tff(c_1841, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1835, c_60])).
% 5.25/2.06  tff(c_1847, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_1841])).
% 5.25/2.06  tff(c_1849, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1847])).
% 5.25/2.06  tff(c_1852, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_1849])).
% 5.25/2.06  tff(c_1856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_1852])).
% 5.25/2.06  tff(c_1857, plain, (v1_xboole_0(u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_1847])).
% 5.25/2.06  tff(c_127, plain, (![A_52]: (r2_hidden(u1_struct_0(A_52), u1_pre_topc(A_52)) | ~v2_pre_topc(A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.25/2.06  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.25/2.06  tff(c_122, plain, (![C_46, B_47, A_48]: (~v1_xboole_0(C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.25/2.06  tff(c_125, plain, (![B_7, A_48, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_48, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_14, c_122])).
% 5.25/2.06  tff(c_153, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | ~r1_tarski(u1_pre_topc(A_62), B_61) | ~v2_pre_topc(A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_127, c_125])).
% 5.25/2.06  tff(c_162, plain, (![A_62]: (~v1_xboole_0(u1_pre_topc(A_62)) | ~v2_pre_topc(A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_6, c_153])).
% 5.25/2.06  tff(c_1861, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1857, c_162])).
% 5.25/2.06  tff(c_1865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_1861])).
% 5.25/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.06  
% 5.25/2.06  Inference rules
% 5.25/2.06  ----------------------
% 5.25/2.06  #Ref     : 0
% 5.25/2.06  #Sup     : 436
% 5.25/2.06  #Fact    : 0
% 5.25/2.06  #Define  : 0
% 5.25/2.06  #Split   : 1
% 5.25/2.06  #Chain   : 0
% 5.25/2.06  #Close   : 0
% 5.25/2.06  
% 5.25/2.06  Ordering : KBO
% 5.25/2.06  
% 5.25/2.06  Simplification rules
% 5.25/2.06  ----------------------
% 5.25/2.06  #Subsume      : 58
% 5.25/2.06  #Demod        : 146
% 5.25/2.06  #Tautology    : 91
% 5.25/2.06  #SimpNegUnit  : 0
% 5.25/2.06  #BackRed      : 0
% 5.25/2.06  
% 5.25/2.06  #Partial instantiations: 0
% 5.25/2.06  #Strategies tried      : 1
% 5.25/2.06  
% 5.25/2.06  Timing (in seconds)
% 5.25/2.06  ----------------------
% 5.25/2.06  Preprocessing        : 0.33
% 5.25/2.06  Parsing              : 0.18
% 5.25/2.06  CNF conversion       : 0.02
% 5.25/2.06  Main loop            : 0.91
% 5.25/2.06  Inferencing          : 0.25
% 5.25/2.06  Reduction            : 0.19
% 5.25/2.06  Demodulation         : 0.12
% 5.25/2.06  BG Simplification    : 0.04
% 5.25/2.06  Subsumption          : 0.38
% 5.25/2.06  Abstraction          : 0.04
% 5.25/2.06  MUC search           : 0.00
% 5.25/2.06  Cooper               : 0.00
% 5.25/2.06  Total                : 1.27
% 5.25/2.06  Index Insertion      : 0.00
% 5.25/2.06  Index Deletion       : 0.00
% 5.25/2.06  Index Matching       : 0.00
% 5.25/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
