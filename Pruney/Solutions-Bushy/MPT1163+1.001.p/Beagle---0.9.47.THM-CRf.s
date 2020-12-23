%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1163+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:32 EST 2020

% Result     : Theorem 33.60s
% Output     : CNFRefutation 33.60s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 324 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k9_subset_1 > k3_orders_2 > k6_domain_1 > k3_xboole_0 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( r1_tarski(C,D)
                     => r1_tarski(k3_orders_2(A,C,B),k3_orders_2(A,D,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_orders_2)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k3_orders_2(A,B,C) = k9_subset_1(u1_struct_0(A),k2_orders_2(A,k6_domain_1(u1_struct_0(A),C)),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_835,plain,(
    ! [A_162,C_163,B_164] :
      ( k9_subset_1(u1_struct_0(A_162),k2_orders_2(A_162,k6_domain_1(u1_struct_0(A_162),C_163)),B_164) = k3_orders_2(A_162,B_164,C_163)
      | ~ m1_subset_1(C_163,u1_struct_0(A_162))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_orders_2(A_162)
      | ~ v5_orders_2(A_162)
      | ~ v4_orders_2(A_162)
      | ~ v3_orders_2(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [A_54,B_55,C_56] :
      ( k9_subset_1(A_54,B_55,C_56) = k3_xboole_0(B_55,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_149,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_4'),B_55,'#skF_6') = k3_xboole_0(B_55,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_143])).

tff(c_842,plain,(
    ! [C_163] :
      ( k3_xboole_0(k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_163)),'#skF_6') = k3_orders_2('#skF_4','#skF_6',C_163)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_149])).

tff(c_860,plain,(
    ! [C_163] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_163))) = k3_orders_2('#skF_4','#skF_6',C_163)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_38,c_2,c_842])).

tff(c_861,plain,(
    ! [C_163] :
      ( k3_xboole_0('#skF_6',k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_163))) = k3_orders_2('#skF_4','#skF_6',C_163)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_860])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_148,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_4'),B_55,'#skF_7') = k3_xboole_0(B_55,'#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_857,plain,(
    ! [C_163] :
      ( k3_xboole_0(k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_163)),'#skF_7') = k3_orders_2('#skF_4','#skF_7',C_163)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_835])).

tff(c_870,plain,(
    ! [C_163] :
      ( k3_xboole_0('#skF_7',k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_163))) = k3_orders_2('#skF_4','#skF_7',C_163)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_36,c_2,c_857])).

tff(c_871,plain,(
    ! [C_163] :
      ( k3_xboole_0('#skF_7',k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_163))) = k3_orders_2('#skF_4','#skF_7',C_163)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_870])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),A_10)
      | r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_104,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,A_46)
      | ~ r2_hidden(D_45,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_187,plain,(
    ! [A_62,B_63,B_64] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_62,B_63),B_64),A_62)
      | r1_tarski(k3_xboole_0(A_62,B_63),B_64) ) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_6,plain,(
    ! [C_14,B_11,A_10] :
      ( r2_hidden(C_14,B_11)
      | ~ r2_hidden(C_14,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_208,plain,(
    ! [A_62,B_63,B_64,B_11] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_62,B_63),B_64),B_11)
      | ~ r1_tarski(A_62,B_11)
      | r1_tarski(k3_xboole_0(A_62,B_63),B_64) ) ),
    inference(resolution,[status(thm)],[c_187,c_6])).

tff(c_92,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [D_20,B_16,A_15] :
      ( r2_hidden(D_20,B_16)
      | ~ r2_hidden(D_20,k3_xboole_0(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    ! [A_15,B_16,B_43] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_15,B_16),B_43),B_16)
      | r1_tarski(k3_xboole_0(A_15,B_16),B_43) ) ),
    inference(resolution,[status(thm)],[c_92,c_14])).

tff(c_120,plain,(
    ! [D_51,A_52,B_53] :
      ( r2_hidden(D_51,k3_xboole_0(A_52,B_53))
      | ~ r2_hidden(D_51,B_53)
      | ~ r2_hidden(D_51,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden('#skF_1'(A_10,B_11),B_11)
      | r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1843,plain,(
    ! [A_216,A_217,B_218] :
      ( r1_tarski(A_216,k3_xboole_0(A_217,B_218))
      | ~ r2_hidden('#skF_1'(A_216,k3_xboole_0(A_217,B_218)),B_218)
      | ~ r2_hidden('#skF_1'(A_216,k3_xboole_0(A_217,B_218)),A_217) ) ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_9270,plain,(
    ! [A_506,B_507,A_508] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_506,B_507),k3_xboole_0(A_508,B_507)),A_508)
      | r1_tarski(k3_xboole_0(A_506,B_507),k3_xboole_0(A_508,B_507)) ) ),
    inference(resolution,[status(thm)],[c_101,c_1843])).

tff(c_10524,plain,(
    ! [A_549,B_550,B_551] :
      ( ~ r1_tarski(A_549,B_550)
      | r1_tarski(k3_xboole_0(A_549,B_551),k3_xboole_0(B_550,B_551)) ) ),
    inference(resolution,[status(thm)],[c_208,c_9270])).

tff(c_55888,plain,(
    ! [A_1451,C_1452] :
      ( ~ r1_tarski(A_1451,'#skF_7')
      | r1_tarski(k3_xboole_0(A_1451,k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_1452))),k3_orders_2('#skF_4','#skF_7',C_1452))
      | ~ m1_subset_1(C_1452,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_10524])).

tff(c_55918,plain,(
    ! [C_163] :
      ( ~ r1_tarski('#skF_6','#skF_7')
      | r1_tarski(k3_orders_2('#skF_4','#skF_6',C_163),k3_orders_2('#skF_4','#skF_7',C_163))
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_55888])).

tff(c_55941,plain,(
    ! [C_1453] :
      ( r1_tarski(k3_orders_2('#skF_4','#skF_6',C_1453),k3_orders_2('#skF_4','#skF_7',C_1453))
      | ~ m1_subset_1(C_1453,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_55918])).

tff(c_32,plain,(
    ~ r1_tarski(k3_orders_2('#skF_4','#skF_6','#skF_5'),k3_orders_2('#skF_4','#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_55962,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_55941,c_32])).

tff(c_55975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_55962])).

%------------------------------------------------------------------------------
