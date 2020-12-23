%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1164+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:32 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :  197 (2334 expanded)
%              Number of leaves         :   35 ( 904 expanded)
%              Depth                    :   21
%              Number of atoms          :  601 (10600 expanded)
%              Number of equality atoms :  122 ( 818 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k9_subset_1 > k3_orders_2 > k6_domain_1 > k3_xboole_0 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_orders_2(C,A,B)
               => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_103,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_113,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_43,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m1_orders_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_98,plain,(
    ! [A_69,B_70,C_71] :
      ( k9_subset_1(A_69,B_70,C_71) = k3_xboole_0(B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_112,plain,(
    ! [B_72] : k9_subset_1(u1_struct_0('#skF_3'),B_72,'#skF_4') = k3_xboole_0(B_72,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_20,plain,(
    ! [A_37] : m1_subset_1('#skF_2'(A_37),A_37) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_65,plain,(
    ! [A_61,B_62,C_63] :
      ( k9_subset_1(A_61,B_62,B_62) = B_62
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_74,plain,(
    ! [A_61,B_62] : k9_subset_1(A_61,B_62,B_62) = B_62 ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_119,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_74])).

tff(c_26,plain,(
    ! [A_45,B_46] : r1_tarski(k3_xboole_0(A_45,B_46),A_45) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_137,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_26])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_40,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_30,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2431,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden('#skF_1'(A_242,B_243,C_244),B_243)
      | ~ m1_orders_2(C_244,A_242,B_243)
      | k1_xboole_0 = B_243
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_orders_2(A_242)
      | ~ v5_orders_2(A_242)
      | ~ v4_orders_2(A_242)
      | ~ v3_orders_2(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4465,plain,(
    ! [A_377,B_378,A_379] :
      ( r2_hidden('#skF_1'(A_377,B_378,A_379),B_378)
      | ~ m1_orders_2(A_379,A_377,B_378)
      | k1_xboole_0 = B_378
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_orders_2(A_377)
      | ~ v5_orders_2(A_377)
      | ~ v4_orders_2(A_377)
      | ~ v3_orders_2(A_377)
      | v2_struct_0(A_377)
      | ~ r1_tarski(A_379,u1_struct_0(A_377)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2431])).

tff(c_4504,plain,(
    ! [A_379] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4',A_379),'#skF_4')
      | ~ m1_orders_2(A_379,'#skF_3','#skF_4')
      | k1_xboole_0 = '#skF_4'
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_379,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_4465])).

tff(c_4560,plain,(
    ! [A_379] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4',A_379),'#skF_4')
      | ~ m1_orders_2(A_379,'#skF_3','#skF_4')
      | k1_xboole_0 = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_379,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_4504])).

tff(c_4561,plain,(
    ! [A_379] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4',A_379),'#skF_4')
      | ~ m1_orders_2(A_379,'#skF_3','#skF_4')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(A_379,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4560])).

tff(c_4796,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4561])).

tff(c_49,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_57,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_639,plain,(
    ! [A_112,C_113,B_114] :
      ( k9_subset_1(u1_struct_0(A_112),k2_orders_2(A_112,k6_domain_1(u1_struct_0(A_112),C_113)),B_114) = k3_orders_2(A_112,B_114,C_113)
      | ~ m1_subset_1(C_113,u1_struct_0(A_112))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_110,plain,(
    ! [B_70] : k9_subset_1(u1_struct_0('#skF_3'),B_70,'#skF_4') = k3_xboole_0(B_70,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_661,plain,(
    ! [C_113] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_113)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_113)
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_110])).

tff(c_699,plain,(
    ! [C_113] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_113)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_113)
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_661])).

tff(c_1146,plain,(
    ! [C_147] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_147)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_147)
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_699])).

tff(c_16,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k9_subset_1(A_30,B_31,C_32),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_122,plain,(
    ! [B_72] :
      ( m1_subset_1(k3_xboole_0(B_72,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_16])).

tff(c_132,plain,(
    ! [B_72] : m1_subset_1(k3_xboole_0(B_72,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122])).

tff(c_1186,plain,(
    ! [C_147] :
      ( m1_subset_1(k3_orders_2('#skF_3','#skF_4',C_147),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_132])).

tff(c_1241,plain,(
    ! [A_154,B_155,D_156] :
      ( m1_orders_2(k3_orders_2(A_154,B_155,D_156),A_154,B_155)
      | ~ r2_hidden(D_156,B_155)
      | ~ m1_subset_1(D_156,u1_struct_0(A_154))
      | k1_xboole_0 = B_155
      | ~ m1_subset_1(k3_orders_2(A_154,B_155,D_156),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v4_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1243,plain,(
    ! [C_147] :
      ( m1_orders_2(k3_orders_2('#skF_3','#skF_4',C_147),'#skF_3','#skF_4')
      | ~ r2_hidden(C_147,'#skF_4')
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1186,c_1241])).

tff(c_1249,plain,(
    ! [C_147] :
      ( m1_orders_2(k3_orders_2('#skF_3','#skF_4',C_147),'#skF_3','#skF_4')
      | ~ r2_hidden(C_147,'#skF_4')
      | k1_xboole_0 = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_1243])).

tff(c_1250,plain,(
    ! [C_147] :
      ( m1_orders_2(k3_orders_2('#skF_3','#skF_4',C_147),'#skF_3','#skF_4')
      | ~ r2_hidden(C_147,'#skF_4')
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1249])).

tff(c_1855,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1250])).

tff(c_355,plain,(
    ! [C_92,A_93] :
      ( k1_xboole_0 = C_92
      | ~ m1_orders_2(C_92,A_93,k1_xboole_0)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_369,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_355])).

tff(c_389,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_369])).

tff(c_390,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_389])).

tff(c_403,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_416,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_403])).

tff(c_1862,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1855,c_416])).

tff(c_1868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1862])).

tff(c_1870,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1250])).

tff(c_256,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_orders_2(C_85,A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_258,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_256])).

tff(c_261,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_258])).

tff(c_262,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_261])).

tff(c_14,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1051,plain,(
    ! [A_140,B_141,C_142] :
      ( k3_orders_2(A_140,B_141,'#skF_1'(A_140,B_141,C_142)) = C_142
      | ~ m1_orders_2(C_142,A_140,B_141)
      | k1_xboole_0 = B_141
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1060,plain,(
    ! [B_141] :
      ( k3_orders_2('#skF_3',B_141,'#skF_1'('#skF_3',B_141,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_141)
      | k1_xboole_0 = B_141
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_262,c_1051])).

tff(c_1085,plain,(
    ! [B_141] :
      ( k3_orders_2('#skF_3',B_141,'#skF_1'('#skF_3',B_141,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_141)
      | k1_xboole_0 = B_141
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_1060])).

tff(c_2274,plain,(
    ! [B_241] :
      ( k3_orders_2('#skF_3',B_241,'#skF_1'('#skF_3',B_241,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_241)
      | k1_xboole_0 = B_241
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1085])).

tff(c_2309,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_2274])).

tff(c_2330,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2309])).

tff(c_2331,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1870,c_2330])).

tff(c_171,plain,(
    ! [B_79,B_80,A_81] :
      ( k9_subset_1(B_79,B_80,A_81) = k3_xboole_0(B_80,A_81)
      | ~ r1_tarski(A_81,B_79) ) ),
    inference(resolution,[status(thm)],[c_30,c_98])).

tff(c_191,plain,(
    ! [B_82] : k9_subset_1('#skF_4',B_82,'#skF_4') = k3_xboole_0(B_82,'#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_171])).

tff(c_75,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k9_subset_1(A_64,B_65,C_66),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_82,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(k9_subset_1(A_64,B_65,C_66),A_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_75,c_28])).

tff(c_197,plain,(
    ! [B_82] :
      ( r1_tarski(k3_xboole_0(B_82,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_82])).

tff(c_216,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_219,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_216])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_219])).

tff(c_224,plain,(
    ! [B_82] : r1_tarski(k3_xboole_0(B_82,'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_1182,plain,(
    ! [C_147] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_4',C_147),'#skF_4')
      | ~ m1_subset_1(C_147,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1146,c_224])).

tff(c_2371,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2331,c_1182])).

tff(c_2383,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2371])).

tff(c_2387,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2383])).

tff(c_2390,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_262,c_34,c_2387])).

tff(c_2392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1870,c_2390])).

tff(c_2394,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_359,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_262,c_355])).

tff(c_379,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_359])).

tff(c_380,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_379])).

tff(c_2486,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_380])).

tff(c_2487,plain,(
    ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2486])).

tff(c_4831,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4796,c_2487])).

tff(c_4856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4831])).

tff(c_4858,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4561])).

tff(c_269,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_262,c_28])).

tff(c_2800,plain,(
    ! [A_269,B_270,C_271] :
      ( k3_orders_2(A_269,B_270,'#skF_1'(A_269,B_270,C_271)) = C_271
      | ~ m1_orders_2(C_271,A_269,B_270)
      | k1_xboole_0 = B_270
      | ~ m1_subset_1(C_271,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_orders_2(A_269)
      | ~ v5_orders_2(A_269)
      | ~ v4_orders_2(A_269)
      | ~ v3_orders_2(A_269)
      | v2_struct_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5150,plain,(
    ! [A_421,B_422,A_423] :
      ( k3_orders_2(A_421,B_422,'#skF_1'(A_421,B_422,A_423)) = A_423
      | ~ m1_orders_2(A_423,A_421,B_422)
      | k1_xboole_0 = B_422
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ l1_orders_2(A_421)
      | ~ v5_orders_2(A_421)
      | ~ v4_orders_2(A_421)
      | ~ v3_orders_2(A_421)
      | v2_struct_0(A_421)
      | ~ r1_tarski(A_423,u1_struct_0(A_421)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2800])).

tff(c_5195,plain,(
    ! [A_423] :
      ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4',A_423)) = A_423
      | ~ m1_orders_2(A_423,'#skF_3','#skF_4')
      | k1_xboole_0 = '#skF_4'
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_423,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_5150])).

tff(c_5260,plain,(
    ! [A_423] :
      ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4',A_423)) = A_423
      | ~ m1_orders_2(A_423,'#skF_3','#skF_4')
      | k1_xboole_0 = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_423,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_5195])).

tff(c_5551,plain,(
    ! [A_443] :
      ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4',A_443)) = A_443
      | ~ m1_orders_2(A_443,'#skF_3','#skF_4')
      | ~ r1_tarski(A_443,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4858,c_5260])).

tff(c_5602,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_269,c_5551])).

tff(c_5638,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5602])).

tff(c_2609,plain,(
    ! [A_254,C_255,B_256] :
      ( k9_subset_1(u1_struct_0(A_254),k2_orders_2(A_254,k6_domain_1(u1_struct_0(A_254),C_255)),B_256) = k3_orders_2(A_254,B_256,C_255)
      | ~ m1_subset_1(C_255,u1_struct_0(A_254))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_orders_2(A_254)
      | ~ v5_orders_2(A_254)
      | ~ v4_orders_2(A_254)
      | ~ v3_orders_2(A_254)
      | v2_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2627,plain,(
    ! [C_255] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_255)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_255)
      | ~ m1_subset_1(C_255,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2609,c_110])).

tff(c_2662,plain,(
    ! [C_255] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_255)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_255)
      | ~ m1_subset_1(C_255,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_2627])).

tff(c_3139,plain,(
    ! [C_291] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_291)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_291)
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2662])).

tff(c_3171,plain,(
    ! [C_291] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_4',C_291),'#skF_4')
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3139,c_224])).

tff(c_5677,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5638,c_3171])).

tff(c_5689,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5677])).

tff(c_5696,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_5689])).

tff(c_5699,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_262,c_34,c_5696])).

tff(c_5701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4858,c_5699])).

tff(c_5702,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_2447,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_1'('#skF_3',B_243,'#skF_4'),B_243)
      | ~ m1_orders_2('#skF_4','#skF_3',B_243)
      | k1_xboole_0 = B_243
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_2431])).

tff(c_2471,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_1'('#skF_3',B_243,'#skF_4'),B_243)
      | ~ m1_orders_2('#skF_4','#skF_3',B_243)
      | k1_xboole_0 = B_243
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_2447])).

tff(c_2472,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_1'('#skF_3',B_243,'#skF_4'),B_243)
      | ~ m1_orders_2('#skF_4','#skF_3',B_243)
      | k1_xboole_0 = B_243
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2471])).

tff(c_6467,plain,(
    ! [B_501] :
      ( r2_hidden('#skF_1'('#skF_3',B_501,'#skF_4'),B_501)
      | ~ m1_orders_2('#skF_4','#skF_3',B_501)
      | B_501 = '#skF_5'
      | ~ m1_subset_1(B_501,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_2472])).

tff(c_6500,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_orders_2('#skF_4','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_6467])).

tff(c_6528,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6500])).

tff(c_5724,plain,(
    ! [A_444,C_445,B_446] :
      ( k9_subset_1(u1_struct_0(A_444),k2_orders_2(A_444,k6_domain_1(u1_struct_0(A_444),C_445)),B_446) = k3_orders_2(A_444,B_446,C_445)
      | ~ m1_subset_1(C_445,u1_struct_0(A_444))
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_orders_2(A_444)
      | ~ v5_orders_2(A_444)
      | ~ v4_orders_2(A_444)
      | ~ v3_orders_2(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5756,plain,(
    ! [C_445] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_445)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_445)
      | ~ m1_subset_1(C_445,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_5724])).

tff(c_5773,plain,(
    ! [C_445] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_445)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_445)
      | ~ m1_subset_1(C_445,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_5756])).

tff(c_6138,plain,(
    ! [C_477] :
      ( k3_xboole_0(k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_477)),'#skF_4') = k3_orders_2('#skF_3','#skF_4',C_477)
      | ~ m1_subset_1(C_477,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5773])).

tff(c_6278,plain,(
    ! [C_490] :
      ( m1_subset_1(k3_orders_2('#skF_3','#skF_4',C_490),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_490,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6138,c_132])).

tff(c_8,plain,(
    ! [A_8,B_20,D_29] :
      ( m1_orders_2(k3_orders_2(A_8,B_20,D_29),A_8,B_20)
      | ~ r2_hidden(D_29,B_20)
      | ~ m1_subset_1(D_29,u1_struct_0(A_8))
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(k3_orders_2(A_8,B_20,D_29),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6254,plain,(
    ! [A_8,B_20,D_29] :
      ( m1_orders_2(k3_orders_2(A_8,B_20,D_29),A_8,B_20)
      | ~ r2_hidden(D_29,B_20)
      | ~ m1_subset_1(D_29,u1_struct_0(A_8))
      | B_20 = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_8,B_20,D_29),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_8])).

tff(c_6280,plain,(
    ! [C_490] :
      ( m1_orders_2(k3_orders_2('#skF_3','#skF_4',C_490),'#skF_3','#skF_4')
      | ~ r2_hidden(C_490,'#skF_4')
      | '#skF_5' = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_490,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6278,c_6254])).

tff(c_6290,plain,(
    ! [C_490] :
      ( m1_orders_2(k3_orders_2('#skF_3','#skF_4',C_490),'#skF_3','#skF_4')
      | ~ r2_hidden(C_490,'#skF_4')
      | '#skF_5' = '#skF_4'
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_490,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_6280])).

tff(c_6291,plain,(
    ! [C_490] :
      ( m1_orders_2(k3_orders_2('#skF_3','#skF_4',C_490),'#skF_3','#skF_4')
      | ~ r2_hidden(C_490,'#skF_4')
      | '#skF_5' = '#skF_4'
      | ~ m1_subset_1(C_490,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6290])).

tff(c_6858,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6291])).

tff(c_5703,plain,(
    m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_5717,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_5703])).

tff(c_6880,plain,(
    m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6858,c_6858,c_5717])).

tff(c_6903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6528,c_6880])).

tff(c_6905,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6291])).

tff(c_5871,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | B_20 = '#skF_5'
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_14])).

tff(c_10,plain,(
    ! [A_8,B_20,C_26] :
      ( k3_orders_2(A_8,B_20,'#skF_1'(A_8,B_20,C_26)) = C_26
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6067,plain,(
    ! [A_470,B_471,C_472] :
      ( k3_orders_2(A_470,B_471,'#skF_1'(A_470,B_471,C_472)) = C_472
      | ~ m1_orders_2(C_472,A_470,B_471)
      | B_471 = '#skF_5'
      | ~ m1_subset_1(C_472,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_orders_2(A_470)
      | ~ v5_orders_2(A_470)
      | ~ v4_orders_2(A_470)
      | ~ v3_orders_2(A_470)
      | v2_struct_0(A_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_10])).

tff(c_6074,plain,(
    ! [B_471] :
      ( k3_orders_2('#skF_3',B_471,'#skF_1'('#skF_3',B_471,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_471)
      | B_471 = '#skF_5'
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_262,c_6067])).

tff(c_6095,plain,(
    ! [B_471] :
      ( k3_orders_2('#skF_3',B_471,'#skF_1'('#skF_3',B_471,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_471)
      | B_471 = '#skF_5'
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_6074])).

tff(c_7708,plain,(
    ! [B_598] :
      ( k3_orders_2('#skF_3',B_598,'#skF_1'('#skF_3',B_598,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_598)
      | B_598 = '#skF_5'
      | ~ m1_subset_1(B_598,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6095])).

tff(c_7746,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_7708])).

tff(c_7773,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7746])).

tff(c_7774,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_6905,c_7773])).

tff(c_6170,plain,(
    ! [C_477] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_4',C_477),'#skF_4')
      | ~ m1_subset_1(C_477,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6138,c_224])).

tff(c_7817,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7774,c_6170])).

tff(c_7832,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_7817])).

tff(c_7836,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5871,c_7832])).

tff(c_7839,plain,
    ( '#skF_5' = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_262,c_34,c_7836])).

tff(c_7841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6905,c_7839])).

tff(c_7843,plain,(
    m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6500])).

tff(c_8262,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6291])).

tff(c_2393,plain,
    ( ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_2484,plain,(
    ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2393])).

tff(c_5716,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_2484])).

tff(c_8288,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8262,c_5716])).

tff(c_8312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7843,c_8288])).

tff(c_8314,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6291])).

tff(c_8901,plain,(
    ! [B_680] :
      ( k3_orders_2('#skF_3',B_680,'#skF_1'('#skF_3',B_680,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_680)
      | B_680 = '#skF_5'
      | ~ m1_subset_1(B_680,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6095])).

tff(c_8939,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_8901])).

tff(c_8966,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8939])).

tff(c_8967,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_8314,c_8966])).

tff(c_9007,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8967,c_6170])).

tff(c_9022,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_9007])).

tff(c_9026,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5871,c_9022])).

tff(c_9029,plain,
    ( '#skF_5' = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_262,c_34,c_9026])).

tff(c_9031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_8314,c_9029])).

tff(c_9032,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2393])).

tff(c_9073,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_9032,c_34,c_9032,c_9032,c_380])).

tff(c_9086,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9073,c_32])).

tff(c_9101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_9086])).

%------------------------------------------------------------------------------
