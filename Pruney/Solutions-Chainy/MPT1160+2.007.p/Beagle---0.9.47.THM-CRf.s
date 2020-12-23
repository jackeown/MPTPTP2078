%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:44 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 217 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_72,axiom,(
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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_102,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_41,plain,(
    ! [A_33] :
      ( k1_struct_0(A_33) = k1_xboole_0
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_50,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_26,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_51,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_74,plain,(
    ! [A_44,B_45,C_46] :
      ( m1_subset_1(k3_orders_2(A_44,B_45,C_46),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(C_46,u1_struct_0(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,(
    ! [A_58,A_59,B_60,C_61] :
      ( m1_subset_1(A_58,u1_struct_0(A_59))
      | ~ r2_hidden(A_58,k3_orders_2(A_59,B_60,C_61))
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_74,c_6])).

tff(c_103,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_59,B_60,C_61)),u1_struct_0(A_59))
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59)
      | k3_orders_2(A_59,B_60,C_61) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_94,plain,(
    ! [B_54,D_55,A_56,C_57] :
      ( r2_hidden(B_54,D_55)
      | ~ r2_hidden(B_54,k3_orders_2(A_56,D_55,C_57))
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(C_57,u1_struct_0(A_56))
      | ~ m1_subset_1(B_54,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_121,plain,(
    ! [A_73,D_74,C_75] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_73,D_74,C_75)),D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_73,D_74,C_75)),u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73)
      | k3_orders_2(A_73,D_74,C_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_94])).

tff(c_125,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_76,B_77,C_78)),B_77)
      | ~ m1_subset_1(C_78,u1_struct_0(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76)
      | k3_orders_2(A_76,B_77,C_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_103,c_121])).

tff(c_58,plain,(
    ! [C_37,B_38,A_39] :
      ( ~ v1_xboole_0(C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    ! [A_1,A_39] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_62,plain,(
    ! [A_39] : ~ r2_hidden(A_39,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_141,plain,(
    ! [C_78,A_76] :
      ( ~ m1_subset_1(C_78,u1_struct_0(A_76))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76)
      | k3_orders_2(A_76,k1_xboole_0,C_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_125,c_62])).

tff(c_149,plain,(
    ! [C_79,A_80] :
      ( ~ m1_subset_1(C_79,u1_struct_0(A_80))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80)
      | k3_orders_2(A_80,k1_xboole_0,C_79) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_141])).

tff(c_155,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_149])).

tff(c_159,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_155])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_38,c_159])).

tff(c_162,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:54:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.26  
% 2.00/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.26  %$ r2_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.00/1.26  
% 2.00/1.26  %Foreground sorts:
% 2.00/1.26  
% 2.00/1.26  
% 2.00/1.26  %Background operators:
% 2.00/1.26  
% 2.00/1.26  
% 2.00/1.26  %Foreground operators:
% 2.00/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.00/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.00/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.00/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.26  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.00/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.00/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.00/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.00/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.00/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.26  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.00/1.26  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.00/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.00/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.26  
% 2.00/1.27  tff(f_119, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 2.00/1.27  tff(f_76, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.00/1.27  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.00/1.27  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.00/1.27  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.00/1.27  tff(f_72, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.00/1.27  tff(f_34, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.00/1.27  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.00/1.27  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.00/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.00/1.27  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.00/1.27  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.27  tff(c_41, plain, (![A_33]: (k1_struct_0(A_33)=k1_xboole_0 | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.00/1.27  tff(c_46, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_18, c_41])).
% 2.00/1.27  tff(c_50, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.00/1.27  tff(c_26, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.00/1.27  tff(c_51, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 2.00/1.27  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.00/1.27  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.00/1.27  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.00/1.27  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.00/1.27  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.00/1.27  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.00/1.27  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.00/1.27  tff(c_74, plain, (![A_44, B_45, C_46]: (m1_subset_1(k3_orders_2(A_44, B_45, C_46), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(C_46, u1_struct_0(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_orders_2(A_44) | ~v5_orders_2(A_44) | ~v4_orders_2(A_44) | ~v3_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.00/1.27  tff(c_6, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.27  tff(c_99, plain, (![A_58, A_59, B_60, C_61]: (m1_subset_1(A_58, u1_struct_0(A_59)) | ~r2_hidden(A_58, k3_orders_2(A_59, B_60, C_61)) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_74, c_6])).
% 2.00/1.27  tff(c_103, plain, (![A_59, B_60, C_61]: (m1_subset_1('#skF_1'(k3_orders_2(A_59, B_60, C_61)), u1_struct_0(A_59)) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59) | k3_orders_2(A_59, B_60, C_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_99])).
% 2.00/1.27  tff(c_94, plain, (![B_54, D_55, A_56, C_57]: (r2_hidden(B_54, D_55) | ~r2_hidden(B_54, k3_orders_2(A_56, D_55, C_57)) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(C_57, u1_struct_0(A_56)) | ~m1_subset_1(B_54, u1_struct_0(A_56)) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.27  tff(c_121, plain, (![A_73, D_74, C_75]: (r2_hidden('#skF_1'(k3_orders_2(A_73, D_74, C_75)), D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_73, D_74, C_75)), u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73) | k3_orders_2(A_73, D_74, C_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_94])).
% 2.00/1.27  tff(c_125, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_1'(k3_orders_2(A_76, B_77, C_78)), B_77) | ~m1_subset_1(C_78, u1_struct_0(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76) | k3_orders_2(A_76, B_77, C_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_103, c_121])).
% 2.00/1.27  tff(c_58, plain, (![C_37, B_38, A_39]: (~v1_xboole_0(C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.00/1.27  tff(c_61, plain, (![A_1, A_39]: (~v1_xboole_0(A_1) | ~r2_hidden(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.00/1.27  tff(c_62, plain, (![A_39]: (~r2_hidden(A_39, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_61])).
% 2.00/1.27  tff(c_141, plain, (![C_78, A_76]: (~m1_subset_1(C_78, u1_struct_0(A_76)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76) | k3_orders_2(A_76, k1_xboole_0, C_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_125, c_62])).
% 2.00/1.27  tff(c_149, plain, (![C_79, A_80]: (~m1_subset_1(C_79, u1_struct_0(A_80)) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80) | k3_orders_2(A_80, k1_xboole_0, C_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_141])).
% 2.00/1.27  tff(c_155, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_149])).
% 2.00/1.27  tff(c_159, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_155])).
% 2.00/1.27  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_38, c_159])).
% 2.00/1.27  tff(c_162, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_61])).
% 2.00/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.00/1.27  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_2])).
% 2.00/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.27  
% 2.00/1.27  Inference rules
% 2.00/1.27  ----------------------
% 2.00/1.27  #Ref     : 0
% 2.00/1.27  #Sup     : 25
% 2.00/1.27  #Fact    : 0
% 2.00/1.27  #Define  : 0
% 2.00/1.27  #Split   : 2
% 2.00/1.27  #Chain   : 0
% 2.00/1.27  #Close   : 0
% 2.00/1.27  
% 2.00/1.27  Ordering : KBO
% 2.00/1.27  
% 2.00/1.27  Simplification rules
% 2.00/1.27  ----------------------
% 2.00/1.27  #Subsume      : 5
% 2.00/1.27  #Demod        : 10
% 2.00/1.27  #Tautology    : 3
% 2.00/1.27  #SimpNegUnit  : 3
% 2.00/1.27  #BackRed      : 2
% 2.00/1.27  
% 2.00/1.27  #Partial instantiations: 0
% 2.00/1.27  #Strategies tried      : 1
% 2.00/1.27  
% 2.00/1.27  Timing (in seconds)
% 2.00/1.27  ----------------------
% 2.00/1.28  Preprocessing        : 0.30
% 2.00/1.28  Parsing              : 0.17
% 2.00/1.28  CNF conversion       : 0.02
% 2.00/1.28  Main loop            : 0.21
% 2.00/1.28  Inferencing          : 0.09
% 2.00/1.28  Reduction            : 0.05
% 2.00/1.28  Demodulation         : 0.04
% 2.00/1.28  BG Simplification    : 0.01
% 2.00/1.28  Subsumption          : 0.04
% 2.00/1.28  Abstraction          : 0.01
% 2.00/1.28  MUC search           : 0.00
% 2.00/1.28  Cooper               : 0.00
% 2.00/1.28  Total                : 0.54
% 2.00/1.28  Index Insertion      : 0.00
% 2.00/1.28  Index Deletion       : 0.00
% 2.00/1.28  Index Matching       : 0.00
% 2.00/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
