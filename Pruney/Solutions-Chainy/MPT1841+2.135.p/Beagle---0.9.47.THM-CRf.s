%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:46 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 168 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  121 ( 351 expanded)
%              Number of equality atoms :   34 (  81 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_yellow_1 > k1_tarski > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_30,plain,(
    ! [A_17] : l1_orders_2(k2_yellow_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [A_19] :
      ( k6_domain_1(A_19,'#skF_4'(A_19)) = A_19
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_4'(A_19),A_19)
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_170,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_198,plain,(
    ! [A_55] :
      ( k6_domain_1(A_55,'#skF_4'(A_55)) = k1_tarski('#skF_4'(A_55))
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_240,plain,(
    ! [A_64] :
      ( k1_tarski('#skF_4'(A_64)) = A_64
      | ~ v1_zfmisc_1(A_64)
      | v1_xboole_0(A_64)
      | ~ v1_zfmisc_1(A_64)
      | v1_xboole_0(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_198])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [B_29,A_30] :
      ( ~ r2_hidden(B_29,A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_83,plain,(
    ! [A_35] :
      ( v1_xboole_0(A_35)
      | r2_hidden('#skF_1'(A_35),A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [A_5] :
      ( '#skF_1'(k1_tarski(A_5)) = A_5
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_83,c_6])).

tff(c_93,plain,(
    ! [A_5] : '#skF_1'(k1_tarski(A_5)) = A_5 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_87])).

tff(c_303,plain,(
    ! [A_68] :
      ( '#skF_4'(A_68) = '#skF_1'(A_68)
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68)
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_93])).

tff(c_305,plain,
    ( '#skF_4'('#skF_5') = '#skF_1'('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_303])).

tff(c_308,plain,
    ( '#skF_4'('#skF_5') = '#skF_1'('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_305])).

tff(c_309,plain,(
    '#skF_4'('#skF_5') = '#skF_1'('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_308])).

tff(c_210,plain,(
    ! [A_19] :
      ( k1_tarski('#skF_4'(A_19)) = A_19
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19)
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_198])).

tff(c_316,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_210])).

tff(c_332,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_316])).

tff(c_333,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_332])).

tff(c_140,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_144,plain,(
    ! [A_5,A_43] :
      ( A_5 = A_43
      | v1_xboole_0(k1_tarski(A_5))
      | ~ m1_subset_1(A_43,k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_150,plain,(
    ! [A_5,A_43] :
      ( A_5 = A_43
      | ~ m1_subset_1(A_43,k1_tarski(A_5)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_144])).

tff(c_395,plain,(
    ! [A_71] :
      ( A_71 = '#skF_1'('#skF_5')
      | ~ m1_subset_1(A_71,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_150])).

tff(c_412,plain,(
    '#skF_1'('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_395])).

tff(c_416,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_333])).

tff(c_176,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_170])).

tff(c_180,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_176])).

tff(c_44,plain,(
    v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_181,plain,(
    v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_44])).

tff(c_428,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_181])).

tff(c_32,plain,(
    ! [A_18] : u1_struct_0(k2_yellow_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_114,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_117,plain,(
    ! [A_17] : u1_struct_0(k2_yellow_1(A_17)) = k2_struct_0(k2_yellow_1(A_17)) ),
    inference(resolution,[status(thm)],[c_30,c_114])).

tff(c_119,plain,(
    ! [A_17] : k2_struct_0(k2_yellow_1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_117])).

tff(c_129,plain,(
    ! [A_40] :
      ( ~ v1_subset_1(k2_struct_0(A_40),u1_struct_0(A_40))
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,(
    ! [A_18] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_18)),A_18)
      | ~ l1_struct_0(k2_yellow_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_129])).

tff(c_137,plain,(
    ! [A_18] :
      ( ~ v1_subset_1(A_18,A_18)
      | ~ l1_struct_0(k2_yellow_1(A_18)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_135])).

tff(c_498,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_428,c_137])).

tff(c_525,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_498])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:45:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.41  
% 2.58/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.41  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_yellow_1 > k1_tarski > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.58/1.41  
% 2.58/1.41  %Foreground sorts:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Background operators:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Foreground operators:
% 2.58/1.41  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.58/1.41  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.58/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.58/1.41  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.58/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.58/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.58/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.58/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.41  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.58/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.58/1.41  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.58/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.58/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.58/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.41  
% 2.58/1.42  tff(f_68, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.58/1.42  tff(f_57, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.58/1.42  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.58/1.42  tff(f_82, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.58/1.42  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.58/1.42  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.58/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.58/1.42  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.58/1.42  tff(f_72, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.58/1.42  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.58/1.42  tff(f_53, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.58/1.42  tff(c_30, plain, (![A_17]: (l1_orders_2(k2_yellow_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.42  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.58/1.42  tff(c_46, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.42  tff(c_48, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.42  tff(c_42, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.42  tff(c_38, plain, (![A_19]: (k6_domain_1(A_19, '#skF_4'(A_19))=A_19 | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.42  tff(c_40, plain, (![A_19]: (m1_subset_1('#skF_4'(A_19), A_19) | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.42  tff(c_170, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.42  tff(c_198, plain, (![A_55]: (k6_domain_1(A_55, '#skF_4'(A_55))=k1_tarski('#skF_4'(A_55)) | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_40, c_170])).
% 2.58/1.42  tff(c_240, plain, (![A_64]: (k1_tarski('#skF_4'(A_64))=A_64 | ~v1_zfmisc_1(A_64) | v1_xboole_0(A_64) | ~v1_zfmisc_1(A_64) | v1_xboole_0(A_64))), inference(superposition, [status(thm), theory('equality')], [c_38, c_198])).
% 2.58/1.42  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.42  tff(c_62, plain, (![B_29, A_30]: (~r2_hidden(B_29, A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.42  tff(c_66, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_62])).
% 2.58/1.42  tff(c_83, plain, (![A_35]: (v1_xboole_0(A_35) | r2_hidden('#skF_1'(A_35), A_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.42  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.42  tff(c_87, plain, (![A_5]: ('#skF_1'(k1_tarski(A_5))=A_5 | v1_xboole_0(k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_83, c_6])).
% 2.58/1.42  tff(c_93, plain, (![A_5]: ('#skF_1'(k1_tarski(A_5))=A_5)), inference(negUnitSimplification, [status(thm)], [c_66, c_87])).
% 2.58/1.42  tff(c_303, plain, (![A_68]: ('#skF_4'(A_68)='#skF_1'(A_68) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(superposition, [status(thm), theory('equality')], [c_240, c_93])).
% 2.58/1.42  tff(c_305, plain, ('#skF_4'('#skF_5')='#skF_1'('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_303])).
% 2.58/1.42  tff(c_308, plain, ('#skF_4'('#skF_5')='#skF_1'('#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_305])).
% 2.58/1.42  tff(c_309, plain, ('#skF_4'('#skF_5')='#skF_1'('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_308])).
% 2.58/1.42  tff(c_210, plain, (![A_19]: (k1_tarski('#skF_4'(A_19))=A_19 | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19) | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(superposition, [status(thm), theory('equality')], [c_38, c_198])).
% 2.58/1.42  tff(c_316, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_309, c_210])).
% 2.58/1.42  tff(c_332, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_316])).
% 2.58/1.42  tff(c_333, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_48, c_332])).
% 2.58/1.42  tff(c_140, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.58/1.42  tff(c_144, plain, (![A_5, A_43]: (A_5=A_43 | v1_xboole_0(k1_tarski(A_5)) | ~m1_subset_1(A_43, k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_140, c_6])).
% 2.58/1.42  tff(c_150, plain, (![A_5, A_43]: (A_5=A_43 | ~m1_subset_1(A_43, k1_tarski(A_5)))), inference(negUnitSimplification, [status(thm)], [c_66, c_144])).
% 2.58/1.42  tff(c_395, plain, (![A_71]: (A_71='#skF_1'('#skF_5') | ~m1_subset_1(A_71, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_333, c_150])).
% 2.58/1.42  tff(c_412, plain, ('#skF_1'('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_395])).
% 2.58/1.42  tff(c_416, plain, (k1_tarski('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_333])).
% 2.58/1.42  tff(c_176, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_170])).
% 2.58/1.42  tff(c_180, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_176])).
% 2.58/1.42  tff(c_44, plain, (v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.42  tff(c_181, plain, (v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_44])).
% 2.58/1.42  tff(c_428, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_181])).
% 2.58/1.42  tff(c_32, plain, (![A_18]: (u1_struct_0(k2_yellow_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.58/1.42  tff(c_109, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.58/1.42  tff(c_114, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_orders_2(A_38))), inference(resolution, [status(thm)], [c_24, c_109])).
% 2.58/1.42  tff(c_117, plain, (![A_17]: (u1_struct_0(k2_yellow_1(A_17))=k2_struct_0(k2_yellow_1(A_17)))), inference(resolution, [status(thm)], [c_30, c_114])).
% 2.58/1.42  tff(c_119, plain, (![A_17]: (k2_struct_0(k2_yellow_1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_117])).
% 2.58/1.42  tff(c_129, plain, (![A_40]: (~v1_subset_1(k2_struct_0(A_40), u1_struct_0(A_40)) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.42  tff(c_135, plain, (![A_18]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_18)), A_18) | ~l1_struct_0(k2_yellow_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_129])).
% 2.58/1.42  tff(c_137, plain, (![A_18]: (~v1_subset_1(A_18, A_18) | ~l1_struct_0(k2_yellow_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_135])).
% 2.58/1.42  tff(c_498, plain, (~l1_struct_0(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_428, c_137])).
% 2.58/1.42  tff(c_525, plain, (~l1_orders_2(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_498])).
% 2.58/1.42  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_525])).
% 2.58/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.42  
% 2.58/1.42  Inference rules
% 2.58/1.42  ----------------------
% 2.58/1.42  #Ref     : 0
% 2.58/1.42  #Sup     : 105
% 2.58/1.42  #Fact    : 0
% 2.58/1.42  #Define  : 0
% 2.58/1.42  #Split   : 0
% 2.58/1.42  #Chain   : 0
% 2.58/1.42  #Close   : 0
% 2.58/1.42  
% 2.58/1.42  Ordering : KBO
% 2.58/1.42  
% 2.58/1.42  Simplification rules
% 2.58/1.42  ----------------------
% 2.58/1.42  #Subsume      : 8
% 2.58/1.42  #Demod        : 65
% 2.58/1.42  #Tautology    : 56
% 2.58/1.42  #SimpNegUnit  : 23
% 2.58/1.42  #BackRed      : 9
% 2.58/1.42  
% 2.58/1.42  #Partial instantiations: 0
% 2.58/1.42  #Strategies tried      : 1
% 2.58/1.42  
% 2.58/1.42  Timing (in seconds)
% 2.58/1.42  ----------------------
% 2.58/1.43  Preprocessing        : 0.32
% 2.58/1.43  Parsing              : 0.17
% 2.58/1.43  CNF conversion       : 0.03
% 2.58/1.43  Main loop            : 0.26
% 2.58/1.43  Inferencing          : 0.10
% 2.58/1.43  Reduction            : 0.08
% 2.58/1.43  Demodulation         : 0.05
% 2.58/1.43  BG Simplification    : 0.02
% 2.58/1.43  Subsumption          : 0.04
% 2.58/1.43  Abstraction          : 0.02
% 2.58/1.43  MUC search           : 0.00
% 2.58/1.43  Cooper               : 0.00
% 2.58/1.43  Total                : 0.62
% 2.58/1.43  Index Insertion      : 0.00
% 2.58/1.43  Index Deletion       : 0.00
% 2.58/1.43  Index Matching       : 0.00
% 2.58/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
