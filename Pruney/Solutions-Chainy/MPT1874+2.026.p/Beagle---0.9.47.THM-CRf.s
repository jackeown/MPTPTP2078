%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:40 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 157 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 440 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_98,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_51,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_89,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,A_51)
      | ~ r2_hidden(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_107,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_101])).

tff(c_218,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_224,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_107,c_218])).

tff(c_237,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_224])).

tff(c_359,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k6_domain_1(A_84,B_85),k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_382,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_359])).

tff(c_394,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_382])).

tff(c_395,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_394])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_254,plain,(
    ! [C_73,A_74,B_75] :
      ( r2_hidden(C_73,A_74)
      | ~ r2_hidden(C_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_801,plain,(
    ! [A_118,B_119,A_120] :
      ( r2_hidden('#skF_2'(A_118,B_119),A_120)
      | ~ m1_subset_1(A_118,k1_zfmisc_1(A_120))
      | r1_tarski(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_10,c_254])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_826,plain,(
    ! [A_121,A_122] :
      ( ~ m1_subset_1(A_121,k1_zfmisc_1(A_122))
      | r1_tarski(A_121,A_122) ) ),
    inference(resolution,[status(thm)],[c_801,c_8])).

tff(c_874,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_395,c_826])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_62,plain,(
    ! [B_42,A_43] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_77,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_233,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_218])).

tff(c_244,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_233])).

tff(c_379,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_359])).

tff(c_391,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_379])).

tff(c_392,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_391])).

tff(c_921,plain,(
    ! [A_123,B_124,C_125] :
      ( k9_subset_1(u1_struct_0(A_123),B_124,k2_pre_topc(A_123,C_125)) = C_125
      | ~ r1_tarski(C_125,B_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_931,plain,(
    ! [B_124] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_124,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_124)
      | ~ v2_tex_2(B_124,'#skF_4')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_392,c_921])).

tff(c_948,plain,(
    ! [B_124] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_124,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_124)
      | ~ v2_tex_2(B_124,'#skF_4')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_931])).

tff(c_1294,plain,(
    ! [B_138] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_138,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_138)
      | ~ v2_tex_2(B_138,'#skF_4')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_948])).

tff(c_36,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_249,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_244,c_36])).

tff(c_1300,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_249])).

tff(c_1308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_874,c_1300])).

tff(c_1310,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1362,plain,(
    ! [C_149,B_150,A_151] :
      ( ~ v1_xboole_0(C_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(C_149))
      | ~ r2_hidden(A_151,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1370,plain,(
    ! [A_151] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_151,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_1362])).

tff(c_1375,plain,(
    ! [A_151] : ~ r2_hidden(A_151,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_1370])).

tff(c_1377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1375,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:52:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.56  
% 3.54/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.56  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.54/1.56  
% 3.54/1.56  %Foreground sorts:
% 3.54/1.56  
% 3.54/1.56  
% 3.54/1.56  %Background operators:
% 3.54/1.56  
% 3.54/1.56  
% 3.54/1.56  %Foreground operators:
% 3.54/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.54/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.54/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.54/1.56  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.54/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.56  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.54/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.54/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.54/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.56  
% 3.54/1.58  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.54/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.54/1.58  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.54/1.58  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.54/1.58  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.54/1.58  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.54/1.58  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.54/1.58  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.54/1.58  tff(f_65, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.54/1.58  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_42, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_51, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.58  tff(c_55, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_51])).
% 3.54/1.58  tff(c_89, plain, (![B_50, A_51]: (m1_subset_1(B_50, A_51) | ~r2_hidden(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.58  tff(c_101, plain, (m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_89])).
% 3.54/1.58  tff(c_107, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_55, c_101])).
% 3.54/1.58  tff(c_218, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.58  tff(c_224, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_107, c_218])).
% 3.54/1.58  tff(c_237, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_55, c_224])).
% 3.54/1.58  tff(c_359, plain, (![A_84, B_85]: (m1_subset_1(k6_domain_1(A_84, B_85), k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.54/1.58  tff(c_382, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_237, c_359])).
% 3.54/1.58  tff(c_394, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_382])).
% 3.54/1.58  tff(c_395, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_55, c_394])).
% 3.54/1.58  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.58  tff(c_254, plain, (![C_73, A_74, B_75]: (r2_hidden(C_73, A_74) | ~r2_hidden(C_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.54/1.58  tff(c_801, plain, (![A_118, B_119, A_120]: (r2_hidden('#skF_2'(A_118, B_119), A_120) | ~m1_subset_1(A_118, k1_zfmisc_1(A_120)) | r1_tarski(A_118, B_119))), inference(resolution, [status(thm)], [c_10, c_254])).
% 3.54/1.58  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.58  tff(c_826, plain, (![A_121, A_122]: (~m1_subset_1(A_121, k1_zfmisc_1(A_122)) | r1_tarski(A_121, A_122))), inference(resolution, [status(thm)], [c_801, c_8])).
% 3.54/1.58  tff(c_874, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_395, c_826])).
% 3.54/1.58  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_62, plain, (![B_42, A_43]: (v1_xboole_0(B_42) | ~m1_subset_1(B_42, A_43) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.58  tff(c_76, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_62])).
% 3.54/1.58  tff(c_77, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_76])).
% 3.54/1.58  tff(c_233, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_218])).
% 3.54/1.58  tff(c_244, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_77, c_233])).
% 3.54/1.58  tff(c_379, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_359])).
% 3.54/1.58  tff(c_391, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_379])).
% 3.54/1.58  tff(c_392, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_77, c_391])).
% 3.54/1.58  tff(c_921, plain, (![A_123, B_124, C_125]: (k9_subset_1(u1_struct_0(A_123), B_124, k2_pre_topc(A_123, C_125))=C_125 | ~r1_tarski(C_125, B_124) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_123))) | ~v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.58  tff(c_931, plain, (![B_124]: (k9_subset_1(u1_struct_0('#skF_4'), B_124, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_124) | ~v2_tex_2(B_124, '#skF_4') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_392, c_921])).
% 3.54/1.58  tff(c_948, plain, (![B_124]: (k9_subset_1(u1_struct_0('#skF_4'), B_124, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_124) | ~v2_tex_2(B_124, '#skF_4') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_931])).
% 3.54/1.58  tff(c_1294, plain, (![B_138]: (k9_subset_1(u1_struct_0('#skF_4'), B_138, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_138) | ~v2_tex_2(B_138, '#skF_4') | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_948])).
% 3.54/1.58  tff(c_36, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.54/1.58  tff(c_249, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_244, c_36])).
% 3.54/1.58  tff(c_1300, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_249])).
% 3.54/1.58  tff(c_1308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_874, c_1300])).
% 3.54/1.58  tff(c_1310, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 3.54/1.58  tff(c_1362, plain, (![C_149, B_150, A_151]: (~v1_xboole_0(C_149) | ~m1_subset_1(B_150, k1_zfmisc_1(C_149)) | ~r2_hidden(A_151, B_150))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.58  tff(c_1370, plain, (![A_151]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_151, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_1362])).
% 3.54/1.58  tff(c_1375, plain, (![A_151]: (~r2_hidden(A_151, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_1370])).
% 3.54/1.58  tff(c_1377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1375, c_38])).
% 3.54/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  Inference rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Ref     : 0
% 3.54/1.58  #Sup     : 298
% 3.54/1.58  #Fact    : 0
% 3.54/1.58  #Define  : 0
% 3.54/1.58  #Split   : 7
% 3.54/1.58  #Chain   : 0
% 3.54/1.58  #Close   : 0
% 3.54/1.58  
% 3.54/1.58  Ordering : KBO
% 3.54/1.58  
% 3.54/1.58  Simplification rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Subsume      : 86
% 3.54/1.58  #Demod        : 64
% 3.54/1.58  #Tautology    : 61
% 3.54/1.58  #SimpNegUnit  : 54
% 3.54/1.58  #BackRed      : 2
% 3.54/1.58  
% 3.54/1.58  #Partial instantiations: 0
% 3.54/1.58  #Strategies tried      : 1
% 3.54/1.58  
% 3.54/1.58  Timing (in seconds)
% 3.54/1.58  ----------------------
% 3.54/1.58  Preprocessing        : 0.32
% 3.54/1.58  Parsing              : 0.16
% 3.54/1.58  CNF conversion       : 0.02
% 3.54/1.58  Main loop            : 0.47
% 3.54/1.58  Inferencing          : 0.17
% 3.54/1.58  Reduction            : 0.14
% 3.54/1.58  Demodulation         : 0.09
% 3.54/1.58  BG Simplification    : 0.02
% 3.54/1.58  Subsumption          : 0.10
% 3.54/1.58  Abstraction          : 0.02
% 3.54/1.58  MUC search           : 0.00
% 3.54/1.58  Cooper               : 0.00
% 3.54/1.58  Total                : 0.83
% 3.54/1.58  Index Insertion      : 0.00
% 3.54/1.58  Index Deletion       : 0.00
% 3.54/1.58  Index Matching       : 0.00
% 3.54/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
