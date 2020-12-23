%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:36 EST 2020

% Result     : Theorem 12.91s
% Output     : CNFRefutation 12.91s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 168 expanded)
%              Number of leaves         :   36 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 416 expanded)
%              Number of equality atoms :   21 (  64 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(c_74,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_76,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_19] :
      ( r2_hidden(u1_struct_0(A_19),u1_pre_topc(A_19))
      | ~ v2_pre_topc(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [A_33] :
      ( m1_subset_1(u1_pre_topc(A_33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33))))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_136,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_231,plain,(
    ! [A_70,A_71] :
      ( r1_tarski(A_70,A_71)
      | v1_xboole_0(k1_zfmisc_1(A_71))
      | ~ m1_subset_1(A_70,k1_zfmisc_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_136,c_12])).

tff(c_798,plain,(
    ! [A_131] :
      ( r1_tarski(u1_pre_topc(A_131),k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131))))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_68,c_231])).

tff(c_28,plain,(
    ! [A_16] : k3_tarski(k1_zfmisc_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_126,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k3_tarski(A_50),k3_tarski(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [A_50,A_16] :
      ( r1_tarski(k3_tarski(A_50),A_16)
      | ~ r1_tarski(A_50,k1_zfmisc_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_126])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,k3_tarski(B_13))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_236,plain,(
    ! [B_72,A_73] :
      ( k3_tarski(B_72) = A_73
      | ~ r1_tarski(k3_tarski(B_72),A_73)
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_259,plain,(
    ! [A_50,A_16] :
      ( k3_tarski(A_50) = A_16
      | ~ r2_hidden(A_16,A_50)
      | ~ r1_tarski(A_50,k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_134,c_236])).

tff(c_3899,plain,(
    ! [A_410] :
      ( k3_tarski(u1_pre_topc(A_410)) = u1_struct_0(A_410)
      | ~ r2_hidden(u1_struct_0(A_410),u1_pre_topc(A_410))
      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_410))))
      | ~ l1_pre_topc(A_410) ) ),
    inference(resolution,[status(thm)],[c_798,c_259])).

tff(c_3907,plain,(
    ! [A_411] :
      ( k3_tarski(u1_pre_topc(A_411)) = u1_struct_0(A_411)
      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_411))))
      | ~ v2_pre_topc(A_411)
      | ~ l1_pre_topc(A_411) ) ),
    inference(resolution,[status(thm)],[c_66,c_3899])).

tff(c_106,plain,(
    ! [C_44,A_45] :
      ( r2_hidden(C_44,k1_zfmisc_1(A_45))
      | ~ r1_tarski(C_44,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_45,C_44] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_45))
      | ~ r1_tarski(C_44,A_45) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_3911,plain,(
    ! [C_412,A_413] :
      ( ~ r1_tarski(C_412,k1_zfmisc_1(u1_struct_0(A_413)))
      | k3_tarski(u1_pre_topc(A_413)) = u1_struct_0(A_413)
      | ~ v2_pre_topc(A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(resolution,[status(thm)],[c_3907,c_114])).

tff(c_3954,plain,(
    ! [A_413] :
      ( k3_tarski(u1_pre_topc(A_413)) = u1_struct_0(A_413)
      | ~ v2_pre_topc(A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(resolution,[status(thm)],[c_10,c_3911])).

tff(c_3955,plain,(
    ! [A_414] :
      ( k3_tarski(u1_pre_topc(A_414)) = u1_struct_0(A_414)
      | ~ v2_pre_topc(A_414)
      | ~ l1_pre_topc(A_414) ) ),
    inference(resolution,[status(thm)],[c_10,c_3911])).

tff(c_70,plain,(
    ! [A_34] :
      ( k4_yellow_0(k2_yellow_1(A_34)) = k3_tarski(A_34)
      | ~ r2_hidden(k3_tarski(A_34),A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11801,plain,(
    ! [A_921] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_921))) = k3_tarski(u1_pre_topc(A_921))
      | ~ r2_hidden(u1_struct_0(A_921),u1_pre_topc(A_921))
      | v1_xboole_0(u1_pre_topc(A_921))
      | ~ v2_pre_topc(A_921)
      | ~ l1_pre_topc(A_921) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3955,c_70])).

tff(c_11810,plain,(
    ! [A_922] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_922))) = k3_tarski(u1_pre_topc(A_922))
      | v1_xboole_0(u1_pre_topc(A_922))
      | ~ v2_pre_topc(A_922)
      | ~ l1_pre_topc(A_922) ) ),
    inference(resolution,[status(thm)],[c_66,c_11801])).

tff(c_72,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_7'))) != u1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11816,plain,
    ( k3_tarski(u1_pre_topc('#skF_7')) != u1_struct_0('#skF_7')
    | v1_xboole_0(u1_pre_topc('#skF_7'))
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_11810,c_72])).

tff(c_11822,plain,
    ( k3_tarski(u1_pre_topc('#skF_7')) != u1_struct_0('#skF_7')
    | v1_xboole_0(u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_11816])).

tff(c_11824,plain,(
    k3_tarski(u1_pre_topc('#skF_7')) != u1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_11822])).

tff(c_11827,plain,
    ( ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3954,c_11824])).

tff(c_11831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_11827])).

tff(c_11832,plain,(
    v1_xboole_0(u1_pre_topc('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_11822])).

tff(c_177,plain,(
    ! [A_62] :
      ( r2_hidden(u1_struct_0(A_62),u1_pre_topc(A_62))
      | ~ v2_pre_topc(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_181,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(u1_pre_topc(A_62))
      | ~ v2_pre_topc(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_11836,plain,
    ( ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_11832,c_181])).

tff(c_11840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_11836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.91/5.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.91/5.42  
% 12.91/5.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.91/5.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_6
% 12.91/5.42  
% 12.91/5.42  %Foreground sorts:
% 12.91/5.42  
% 12.91/5.42  
% 12.91/5.42  %Background operators:
% 12.91/5.42  
% 12.91/5.42  
% 12.91/5.42  %Foreground operators:
% 12.91/5.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.91/5.42  tff('#skF_5', type, '#skF_5': $i > $i).
% 12.91/5.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.91/5.42  tff('#skF_4', type, '#skF_4': $i > $i).
% 12.91/5.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.91/5.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.91/5.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.91/5.42  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 12.91/5.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.91/5.42  tff('#skF_7', type, '#skF_7': $i).
% 12.91/5.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.91/5.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.91/5.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.91/5.42  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 12.91/5.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.91/5.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.91/5.42  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 12.91/5.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.91/5.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.91/5.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.91/5.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.91/5.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.91/5.42  tff('#skF_6', type, '#skF_6': $i > $i).
% 12.91/5.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.91/5.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.91/5.42  
% 12.91/5.44  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 12.91/5.44  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.91/5.44  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 12.91/5.44  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 12.91/5.44  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 12.91/5.44  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.91/5.44  tff(f_54, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 12.91/5.44  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 12.91/5.44  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 12.91/5.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.91/5.44  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 12.91/5.44  tff(c_74, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.91/5.44  tff(c_76, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.91/5.44  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.91/5.44  tff(c_66, plain, (![A_19]: (r2_hidden(u1_struct_0(A_19), u1_pre_topc(A_19)) | ~v2_pre_topc(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.91/5.44  tff(c_68, plain, (![A_33]: (m1_subset_1(u1_pre_topc(A_33), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33)))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.91/5.44  tff(c_136, plain, (![A_52, B_53]: (r2_hidden(A_52, B_53) | v1_xboole_0(B_53) | ~m1_subset_1(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.91/5.44  tff(c_12, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.91/5.44  tff(c_231, plain, (![A_70, A_71]: (r1_tarski(A_70, A_71) | v1_xboole_0(k1_zfmisc_1(A_71)) | ~m1_subset_1(A_70, k1_zfmisc_1(A_71)))), inference(resolution, [status(thm)], [c_136, c_12])).
% 12.91/5.44  tff(c_798, plain, (![A_131]: (r1_tarski(u1_pre_topc(A_131), k1_zfmisc_1(u1_struct_0(A_131))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131)))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_68, c_231])).
% 12.91/5.44  tff(c_28, plain, (![A_16]: (k3_tarski(k1_zfmisc_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.91/5.44  tff(c_126, plain, (![A_50, B_51]: (r1_tarski(k3_tarski(A_50), k3_tarski(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.91/5.44  tff(c_134, plain, (![A_50, A_16]: (r1_tarski(k3_tarski(A_50), A_16) | ~r1_tarski(A_50, k1_zfmisc_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_126])).
% 12.91/5.44  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, k3_tarski(B_13)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.91/5.44  tff(c_116, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.91/5.44  tff(c_236, plain, (![B_72, A_73]: (k3_tarski(B_72)=A_73 | ~r1_tarski(k3_tarski(B_72), A_73) | ~r2_hidden(A_73, B_72))), inference(resolution, [status(thm)], [c_24, c_116])).
% 12.91/5.44  tff(c_259, plain, (![A_50, A_16]: (k3_tarski(A_50)=A_16 | ~r2_hidden(A_16, A_50) | ~r1_tarski(A_50, k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_134, c_236])).
% 12.91/5.44  tff(c_3899, plain, (![A_410]: (k3_tarski(u1_pre_topc(A_410))=u1_struct_0(A_410) | ~r2_hidden(u1_struct_0(A_410), u1_pre_topc(A_410)) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_410)))) | ~l1_pre_topc(A_410))), inference(resolution, [status(thm)], [c_798, c_259])).
% 12.91/5.44  tff(c_3907, plain, (![A_411]: (k3_tarski(u1_pre_topc(A_411))=u1_struct_0(A_411) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_411)))) | ~v2_pre_topc(A_411) | ~l1_pre_topc(A_411))), inference(resolution, [status(thm)], [c_66, c_3899])).
% 12.91/5.44  tff(c_106, plain, (![C_44, A_45]: (r2_hidden(C_44, k1_zfmisc_1(A_45)) | ~r1_tarski(C_44, A_45))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.91/5.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.91/5.44  tff(c_114, plain, (![A_45, C_44]: (~v1_xboole_0(k1_zfmisc_1(A_45)) | ~r1_tarski(C_44, A_45))), inference(resolution, [status(thm)], [c_106, c_2])).
% 12.91/5.44  tff(c_3911, plain, (![C_412, A_413]: (~r1_tarski(C_412, k1_zfmisc_1(u1_struct_0(A_413))) | k3_tarski(u1_pre_topc(A_413))=u1_struct_0(A_413) | ~v2_pre_topc(A_413) | ~l1_pre_topc(A_413))), inference(resolution, [status(thm)], [c_3907, c_114])).
% 12.91/5.44  tff(c_3954, plain, (![A_413]: (k3_tarski(u1_pre_topc(A_413))=u1_struct_0(A_413) | ~v2_pre_topc(A_413) | ~l1_pre_topc(A_413))), inference(resolution, [status(thm)], [c_10, c_3911])).
% 12.91/5.44  tff(c_3955, plain, (![A_414]: (k3_tarski(u1_pre_topc(A_414))=u1_struct_0(A_414) | ~v2_pre_topc(A_414) | ~l1_pre_topc(A_414))), inference(resolution, [status(thm)], [c_10, c_3911])).
% 12.91/5.44  tff(c_70, plain, (![A_34]: (k4_yellow_0(k2_yellow_1(A_34))=k3_tarski(A_34) | ~r2_hidden(k3_tarski(A_34), A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.91/5.44  tff(c_11801, plain, (![A_921]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_921)))=k3_tarski(u1_pre_topc(A_921)) | ~r2_hidden(u1_struct_0(A_921), u1_pre_topc(A_921)) | v1_xboole_0(u1_pre_topc(A_921)) | ~v2_pre_topc(A_921) | ~l1_pre_topc(A_921))), inference(superposition, [status(thm), theory('equality')], [c_3955, c_70])).
% 12.91/5.44  tff(c_11810, plain, (![A_922]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_922)))=k3_tarski(u1_pre_topc(A_922)) | v1_xboole_0(u1_pre_topc(A_922)) | ~v2_pre_topc(A_922) | ~l1_pre_topc(A_922))), inference(resolution, [status(thm)], [c_66, c_11801])).
% 12.91/5.44  tff(c_72, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_7')))!=u1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.91/5.44  tff(c_11816, plain, (k3_tarski(u1_pre_topc('#skF_7'))!=u1_struct_0('#skF_7') | v1_xboole_0(u1_pre_topc('#skF_7')) | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11810, c_72])).
% 12.91/5.44  tff(c_11822, plain, (k3_tarski(u1_pre_topc('#skF_7'))!=u1_struct_0('#skF_7') | v1_xboole_0(u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_11816])).
% 12.91/5.44  tff(c_11824, plain, (k3_tarski(u1_pre_topc('#skF_7'))!=u1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_11822])).
% 12.91/5.44  tff(c_11827, plain, (~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3954, c_11824])).
% 12.91/5.44  tff(c_11831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_11827])).
% 12.91/5.44  tff(c_11832, plain, (v1_xboole_0(u1_pre_topc('#skF_7'))), inference(splitRight, [status(thm)], [c_11822])).
% 12.91/5.44  tff(c_177, plain, (![A_62]: (r2_hidden(u1_struct_0(A_62), u1_pre_topc(A_62)) | ~v2_pre_topc(A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.91/5.44  tff(c_181, plain, (![A_62]: (~v1_xboole_0(u1_pre_topc(A_62)) | ~v2_pre_topc(A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_177, c_2])).
% 12.91/5.44  tff(c_11836, plain, (~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_11832, c_181])).
% 12.91/5.44  tff(c_11840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_11836])).
% 12.91/5.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.91/5.44  
% 12.91/5.44  Inference rules
% 12.91/5.44  ----------------------
% 12.91/5.44  #Ref     : 0
% 12.91/5.44  #Sup     : 2736
% 12.91/5.44  #Fact    : 0
% 12.91/5.44  #Define  : 0
% 12.91/5.44  #Split   : 1
% 13.13/5.44  #Chain   : 0
% 13.13/5.44  #Close   : 0
% 13.13/5.44  
% 13.13/5.44  Ordering : KBO
% 13.13/5.44  
% 13.13/5.44  Simplification rules
% 13.13/5.44  ----------------------
% 13.13/5.44  #Subsume      : 284
% 13.13/5.44  #Demod        : 602
% 13.13/5.44  #Tautology    : 214
% 13.13/5.44  #SimpNegUnit  : 0
% 13.13/5.44  #BackRed      : 0
% 13.13/5.44  
% 13.13/5.44  #Partial instantiations: 0
% 13.13/5.44  #Strategies tried      : 1
% 13.13/5.44  
% 13.13/5.44  Timing (in seconds)
% 13.13/5.44  ----------------------
% 13.13/5.44  Preprocessing        : 0.32
% 13.13/5.44  Parsing              : 0.17
% 13.13/5.44  CNF conversion       : 0.03
% 13.13/5.44  Main loop            : 4.36
% 13.13/5.44  Inferencing          : 0.74
% 13.13/5.44  Reduction            : 0.59
% 13.13/5.44  Demodulation         : 0.37
% 13.13/5.44  BG Simplification    : 0.11
% 13.13/5.44  Subsumption          : 2.68
% 13.13/5.44  Abstraction          : 0.13
% 13.13/5.44  MUC search           : 0.00
% 13.13/5.44  Cooper               : 0.00
% 13.13/5.44  Total                : 4.71
% 13.13/5.44  Index Insertion      : 0.00
% 13.13/5.44  Index Deletion       : 0.00
% 13.13/5.44  Index Matching       : 0.00
% 13.13/5.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
