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
% DateTime   : Thu Dec  3 10:19:45 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   63 (  76 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 ( 241 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_67,plain,(
    ! [A_37] :
      ( k1_struct_0(A_37) = k1_xboole_0
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,(
    ! [A_43] :
      ( k1_struct_0(A_43) = k1_xboole_0
      | ~ l1_orders_2(A_43) ) ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_95,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_30,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_96,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_30])).

tff(c_40,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k3_orders_2(A_13,B_14,C_15),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(C_15,u1_struct_0(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13)
      | ~ v4_orders_2(A_13)
      | ~ v3_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | k1_xboole_0 = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k3_orders_2(A_54,B_55,C_56),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(C_56,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_139,plain,(
    ! [A_64,A_65,B_66,C_67] :
      ( m1_subset_1(A_64,u1_struct_0(A_65))
      | ~ r2_hidden(A_64,k3_orders_2(A_65,B_66,C_67))
      | ~ m1_subset_1(C_67,u1_struct_0(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_125,c_16])).

tff(c_143,plain,(
    ! [A_5,A_65,B_66,C_67] :
      ( m1_subset_1('#skF_1'(A_5,k3_orders_2(A_65,B_66,C_67)),u1_struct_0(A_65))
      | ~ m1_subset_1(C_67,u1_struct_0(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65)
      | k3_orders_2(A_65,B_66,C_67) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_65,B_66,C_67),k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_134,plain,(
    ! [B_60,D_61,A_62,C_63] :
      ( r2_hidden(B_60,D_61)
      | ~ r2_hidden(B_60,k3_orders_2(A_62,D_61,C_63))
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(C_63,u1_struct_0(A_62))
      | ~ m1_subset_1(B_60,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v5_orders_2(A_62)
      | ~ v4_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_192,plain,(
    ! [A_93,A_94,D_95,C_96] :
      ( r2_hidden('#skF_1'(A_93,k3_orders_2(A_94,D_95,C_96)),D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(C_96,u1_struct_0(A_94))
      | ~ m1_subset_1('#skF_1'(A_93,k3_orders_2(A_94,D_95,C_96)),u1_struct_0(A_94))
      | ~ l1_orders_2(A_94)
      | ~ v5_orders_2(A_94)
      | ~ v4_orders_2(A_94)
      | ~ v3_orders_2(A_94)
      | v2_struct_0(A_94)
      | k3_orders_2(A_94,D_95,C_96) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_94,D_95,C_96),k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_10,c_134])).

tff(c_200,plain,(
    ! [A_97,A_98,B_99,C_100] :
      ( r2_hidden('#skF_1'(A_97,k3_orders_2(A_98,B_99,C_100)),B_99)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98)
      | k3_orders_2(A_98,B_99,C_100) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_98,B_99,C_100),k1_zfmisc_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_143,c_192])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_38,B_39] : ~ r2_hidden(A_38,k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_72])).

tff(c_221,plain,(
    ! [C_100,A_98,A_97] :
      ( ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98)
      | k3_orders_2(A_98,k1_xboole_0,C_100) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_98,k1_xboole_0,C_100),k1_zfmisc_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_200,c_75])).

tff(c_238,plain,(
    ! [C_105,A_106,A_107] :
      ( ~ m1_subset_1(C_105,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106)
      | k3_orders_2(A_106,k1_xboole_0,C_105) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_106,k1_xboole_0,C_105),k1_zfmisc_1(A_107)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_221])).

tff(c_242,plain,(
    ! [A_13,C_15] :
      ( k3_orders_2(A_13,k1_xboole_0,C_15) = k1_xboole_0
      | ~ m1_subset_1(C_15,u1_struct_0(A_13))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13)
      | ~ v4_orders_2(A_13)
      | ~ v3_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_238])).

tff(c_246,plain,(
    ! [A_108,C_109] :
      ( k3_orders_2(A_108,k1_xboole_0,C_109) = k1_xboole_0
      | ~ m1_subset_1(C_109,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_242])).

tff(c_260,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_246])).

tff(c_266,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_260])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_96,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.32  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.43/1.32  
% 2.43/1.32  %Foreground sorts:
% 2.43/1.32  
% 2.43/1.32  
% 2.43/1.32  %Background operators:
% 2.43/1.32  
% 2.43/1.32  
% 2.43/1.32  %Foreground operators:
% 2.43/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.43/1.32  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.32  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.43/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.43/1.32  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.43/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.43/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.32  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.43/1.32  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.43/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.32  
% 2.43/1.33  tff(f_122, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 2.43/1.33  tff(f_79, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.43/1.33  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.43/1.33  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.43/1.33  tff(f_75, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.43/1.33  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.43/1.33  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.43/1.33  tff(f_105, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.43/1.33  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.43/1.33  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.43/1.33  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.43/1.33  tff(c_34, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.43/1.33  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.43/1.33  tff(c_67, plain, (![A_37]: (k1_struct_0(A_37)=k1_xboole_0 | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.33  tff(c_91, plain, (![A_43]: (k1_struct_0(A_43)=k1_xboole_0 | ~l1_orders_2(A_43))), inference(resolution, [status(thm)], [c_22, c_67])).
% 2.43/1.33  tff(c_95, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_91])).
% 2.43/1.33  tff(c_30, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.43/1.33  tff(c_96, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_95, c_30])).
% 2.43/1.33  tff(c_40, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.43/1.33  tff(c_38, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.43/1.33  tff(c_36, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.43/1.33  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.43/1.33  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.43/1.33  tff(c_20, plain, (![A_13, B_14, C_15]: (m1_subset_1(k3_orders_2(A_13, B_14, C_15), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(C_15, u1_struct_0(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13) | ~v4_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.33  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | k1_xboole_0=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.33  tff(c_125, plain, (![A_54, B_55, C_56]: (m1_subset_1(k3_orders_2(A_54, B_55, C_56), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(C_56, u1_struct_0(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.33  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.33  tff(c_139, plain, (![A_64, A_65, B_66, C_67]: (m1_subset_1(A_64, u1_struct_0(A_65)) | ~r2_hidden(A_64, k3_orders_2(A_65, B_66, C_67)) | ~m1_subset_1(C_67, u1_struct_0(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_125, c_16])).
% 2.43/1.33  tff(c_143, plain, (![A_5, A_65, B_66, C_67]: (m1_subset_1('#skF_1'(A_5, k3_orders_2(A_65, B_66, C_67)), u1_struct_0(A_65)) | ~m1_subset_1(C_67, u1_struct_0(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65) | k3_orders_2(A_65, B_66, C_67)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_65, B_66, C_67), k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_10, c_139])).
% 2.43/1.33  tff(c_134, plain, (![B_60, D_61, A_62, C_63]: (r2_hidden(B_60, D_61) | ~r2_hidden(B_60, k3_orders_2(A_62, D_61, C_63)) | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(C_63, u1_struct_0(A_62)) | ~m1_subset_1(B_60, u1_struct_0(A_62)) | ~l1_orders_2(A_62) | ~v5_orders_2(A_62) | ~v4_orders_2(A_62) | ~v3_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.43/1.33  tff(c_192, plain, (![A_93, A_94, D_95, C_96]: (r2_hidden('#skF_1'(A_93, k3_orders_2(A_94, D_95, C_96)), D_95) | ~m1_subset_1(D_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(C_96, u1_struct_0(A_94)) | ~m1_subset_1('#skF_1'(A_93, k3_orders_2(A_94, D_95, C_96)), u1_struct_0(A_94)) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94) | k3_orders_2(A_94, D_95, C_96)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_94, D_95, C_96), k1_zfmisc_1(A_93)))), inference(resolution, [status(thm)], [c_10, c_134])).
% 2.43/1.33  tff(c_200, plain, (![A_97, A_98, B_99, C_100]: (r2_hidden('#skF_1'(A_97, k3_orders_2(A_98, B_99, C_100)), B_99) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98) | k3_orders_2(A_98, B_99, C_100)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_98, B_99, C_100), k1_zfmisc_1(A_97)))), inference(resolution, [status(thm)], [c_143, c_192])).
% 2.43/1.33  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.33  tff(c_72, plain, (![A_38, B_39]: (~r2_hidden(A_38, k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.33  tff(c_75, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_72])).
% 2.43/1.33  tff(c_221, plain, (![C_100, A_98, A_97]: (~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98) | k3_orders_2(A_98, k1_xboole_0, C_100)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_98, k1_xboole_0, C_100), k1_zfmisc_1(A_97)))), inference(resolution, [status(thm)], [c_200, c_75])).
% 2.43/1.33  tff(c_238, plain, (![C_105, A_106, A_107]: (~m1_subset_1(C_105, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106) | k3_orders_2(A_106, k1_xboole_0, C_105)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_106, k1_xboole_0, C_105), k1_zfmisc_1(A_107)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_221])).
% 2.43/1.33  tff(c_242, plain, (![A_13, C_15]: (k3_orders_2(A_13, k1_xboole_0, C_15)=k1_xboole_0 | ~m1_subset_1(C_15, u1_struct_0(A_13)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13) | ~v4_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(resolution, [status(thm)], [c_20, c_238])).
% 2.43/1.33  tff(c_246, plain, (![A_108, C_109]: (k3_orders_2(A_108, k1_xboole_0, C_109)=k1_xboole_0 | ~m1_subset_1(C_109, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_242])).
% 2.43/1.33  tff(c_260, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_246])).
% 2.43/1.33  tff(c_266, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_260])).
% 2.43/1.33  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_96, c_266])).
% 2.43/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.33  
% 2.43/1.33  Inference rules
% 2.43/1.33  ----------------------
% 2.43/1.33  #Ref     : 0
% 2.43/1.33  #Sup     : 49
% 2.43/1.33  #Fact    : 0
% 2.43/1.33  #Define  : 0
% 2.43/1.33  #Split   : 0
% 2.43/1.33  #Chain   : 0
% 2.43/1.33  #Close   : 0
% 2.43/1.33  
% 2.43/1.33  Ordering : KBO
% 2.43/1.33  
% 2.43/1.33  Simplification rules
% 2.43/1.33  ----------------------
% 2.43/1.33  #Subsume      : 7
% 2.43/1.33  #Demod        : 8
% 2.43/1.33  #Tautology    : 15
% 2.43/1.33  #SimpNegUnit  : 1
% 2.43/1.33  #BackRed      : 1
% 2.43/1.33  
% 2.43/1.33  #Partial instantiations: 0
% 2.43/1.33  #Strategies tried      : 1
% 2.43/1.33  
% 2.43/1.33  Timing (in seconds)
% 2.43/1.33  ----------------------
% 2.43/1.34  Preprocessing        : 0.30
% 2.43/1.34  Parsing              : 0.17
% 2.43/1.34  CNF conversion       : 0.02
% 2.70/1.34  Main loop            : 0.26
% 2.70/1.34  Inferencing          : 0.10
% 2.70/1.34  Reduction            : 0.06
% 2.70/1.34  Demodulation         : 0.04
% 2.70/1.34  BG Simplification    : 0.02
% 2.70/1.34  Subsumption          : 0.06
% 2.70/1.34  Abstraction          : 0.01
% 2.70/1.34  MUC search           : 0.00
% 2.70/1.34  Cooper               : 0.00
% 2.70/1.34  Total                : 0.59
% 2.70/1.34  Index Insertion      : 0.00
% 2.70/1.34  Index Deletion       : 0.00
% 2.70/1.34  Index Matching       : 0.00
% 2.70/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
