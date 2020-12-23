%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:26 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 123 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 345 expanded)
%              Number of equality atoms :    5 (  24 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ? [E] :
                          ( m1_subset_1(E,u1_struct_0(C))
                          & E = D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    ! [B_58,A_59] :
      ( l1_pre_topc(B_58)
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_66])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_69])).

tff(c_30,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_103,plain,(
    ! [B_76,A_77] :
      ( m1_subset_1(u1_struct_0(B_76),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(u1_struct_0(B_78),u1_struct_0(A_79))
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_103,c_26])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_127,plain,(
    ! [B_83,A_84] :
      ( k2_xboole_0(u1_struct_0(B_83),u1_struct_0(A_84)) = u1_struct_0(A_84)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_108,c_20])).

tff(c_86,plain,(
    ! [D_62,A_63,B_64] :
      ( ~ r2_hidden(D_62,A_63)
      | r2_hidden(D_62,k2_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    ! [D_62,A_63,B_64] :
      ( m1_subset_1(D_62,k2_xboole_0(A_63,B_64))
      | ~ r2_hidden(D_62,A_63) ) ),
    inference(resolution,[status(thm)],[c_86,c_22])).

tff(c_169,plain,(
    ! [D_91,A_92,B_93] :
      ( m1_subset_1(D_91,u1_struct_0(A_92))
      | ~ r2_hidden(D_91,u1_struct_0(B_93))
      | ~ m1_pre_topc(B_93,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_90])).

tff(c_1578,plain,(
    ! [A_175,A_176,B_177] :
      ( m1_subset_1(A_175,u1_struct_0(A_176))
      | ~ m1_pre_topc(B_177,A_176)
      | ~ l1_pre_topc(A_176)
      | v1_xboole_0(u1_struct_0(B_177))
      | ~ m1_subset_1(A_175,u1_struct_0(B_177)) ) ),
    inference(resolution,[status(thm)],[c_24,c_169])).

tff(c_1580,plain,(
    ! [A_175] :
      ( m1_subset_1(A_175,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_175,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1578])).

tff(c_1587,plain,(
    ! [A_175] :
      ( m1_subset_1(A_175,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_175,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1580])).

tff(c_1594,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1587])).

tff(c_34,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1646,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1594,c_34])).

tff(c_1649,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1646])).

tff(c_1652,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1649])).

tff(c_1656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1652])).

tff(c_1658,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1587])).

tff(c_44,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_81,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_72])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1584,plain,(
    ! [A_175] :
      ( m1_subset_1(A_175,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_175,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1578])).

tff(c_1593,plain,(
    ! [A_175] :
      ( m1_subset_1(A_175,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_175,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1584])).

tff(c_1729,plain,(
    ! [A_186] :
      ( m1_subset_1(A_186,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_186,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1658,c_1593])).

tff(c_38,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1735,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1729,c_38])).

tff(c_1740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.68  
% 3.96/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.68  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.96/1.68  
% 3.96/1.68  %Foreground sorts:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Background operators:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Foreground operators:
% 3.96/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.96/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.96/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.96/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.96/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.96/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.96/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.96/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.96/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.96/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.96/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.68  
% 3.96/1.69  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tmap_1)).
% 3.96/1.69  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.96/1.69  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.96/1.69  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.96/1.69  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.96/1.69  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.96/1.69  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.96/1.69  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.96/1.69  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.96/1.69  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.96/1.69  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/1.69  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/1.69  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/1.69  tff(c_66, plain, (![B_58, A_59]: (l1_pre_topc(B_58) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.96/1.69  tff(c_69, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_66])).
% 3.96/1.69  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_69])).
% 3.96/1.69  tff(c_30, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.96/1.69  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/1.69  tff(c_24, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.96/1.69  tff(c_103, plain, (![B_76, A_77]: (m1_subset_1(u1_struct_0(B_76), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.96/1.69  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.96/1.69  tff(c_108, plain, (![B_78, A_79]: (r1_tarski(u1_struct_0(B_78), u1_struct_0(A_79)) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_103, c_26])).
% 3.96/1.69  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.96/1.69  tff(c_127, plain, (![B_83, A_84]: (k2_xboole_0(u1_struct_0(B_83), u1_struct_0(A_84))=u1_struct_0(A_84) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_108, c_20])).
% 3.96/1.69  tff(c_86, plain, (![D_62, A_63, B_64]: (~r2_hidden(D_62, A_63) | r2_hidden(D_62, k2_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.96/1.69  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.96/1.69  tff(c_90, plain, (![D_62, A_63, B_64]: (m1_subset_1(D_62, k2_xboole_0(A_63, B_64)) | ~r2_hidden(D_62, A_63))), inference(resolution, [status(thm)], [c_86, c_22])).
% 3.96/1.69  tff(c_169, plain, (![D_91, A_92, B_93]: (m1_subset_1(D_91, u1_struct_0(A_92)) | ~r2_hidden(D_91, u1_struct_0(B_93)) | ~m1_pre_topc(B_93, A_92) | ~l1_pre_topc(A_92))), inference(superposition, [status(thm), theory('equality')], [c_127, c_90])).
% 3.96/1.69  tff(c_1578, plain, (![A_175, A_176, B_177]: (m1_subset_1(A_175, u1_struct_0(A_176)) | ~m1_pre_topc(B_177, A_176) | ~l1_pre_topc(A_176) | v1_xboole_0(u1_struct_0(B_177)) | ~m1_subset_1(A_175, u1_struct_0(B_177)))), inference(resolution, [status(thm)], [c_24, c_169])).
% 3.96/1.69  tff(c_1580, plain, (![A_175]: (m1_subset_1(A_175, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_175, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_48, c_1578])).
% 3.96/1.69  tff(c_1587, plain, (![A_175]: (m1_subset_1(A_175, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_175, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1580])).
% 3.96/1.69  tff(c_1594, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1587])).
% 3.96/1.69  tff(c_34, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.96/1.69  tff(c_1646, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1594, c_34])).
% 3.96/1.69  tff(c_1649, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_1646])).
% 3.96/1.69  tff(c_1652, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1649])).
% 3.96/1.69  tff(c_1656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_1652])).
% 3.96/1.69  tff(c_1658, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1587])).
% 3.96/1.69  tff(c_44, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/1.69  tff(c_72, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.96/1.69  tff(c_81, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_72])).
% 3.96/1.69  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/1.69  tff(c_1584, plain, (![A_175]: (m1_subset_1(A_175, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_175, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_1578])).
% 3.96/1.69  tff(c_1593, plain, (![A_175]: (m1_subset_1(A_175, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_175, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1584])).
% 3.96/1.69  tff(c_1729, plain, (![A_186]: (m1_subset_1(A_186, u1_struct_0('#skF_5')) | ~m1_subset_1(A_186, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1658, c_1593])).
% 3.96/1.69  tff(c_38, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.96/1.69  tff(c_1735, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1729, c_38])).
% 3.96/1.69  tff(c_1740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1735])).
% 3.96/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.69  
% 3.96/1.69  Inference rules
% 3.96/1.69  ----------------------
% 3.96/1.69  #Ref     : 0
% 3.96/1.69  #Sup     : 338
% 3.96/1.69  #Fact    : 6
% 3.96/1.69  #Define  : 0
% 3.96/1.69  #Split   : 2
% 3.96/1.69  #Chain   : 0
% 3.96/1.69  #Close   : 0
% 3.96/1.69  
% 3.96/1.69  Ordering : KBO
% 3.96/1.69  
% 3.96/1.69  Simplification rules
% 3.96/1.69  ----------------------
% 3.96/1.69  #Subsume      : 38
% 3.96/1.69  #Demod        : 52
% 3.96/1.69  #Tautology    : 63
% 3.96/1.69  #SimpNegUnit  : 3
% 3.96/1.69  #BackRed      : 2
% 3.96/1.69  
% 3.96/1.69  #Partial instantiations: 0
% 3.96/1.69  #Strategies tried      : 1
% 3.96/1.69  
% 3.96/1.69  Timing (in seconds)
% 3.96/1.69  ----------------------
% 3.96/1.70  Preprocessing        : 0.30
% 3.96/1.70  Parsing              : 0.17
% 3.96/1.70  CNF conversion       : 0.02
% 3.96/1.70  Main loop            : 0.59
% 3.96/1.70  Inferencing          : 0.22
% 3.96/1.70  Reduction            : 0.13
% 3.96/1.70  Demodulation         : 0.08
% 3.96/1.70  BG Simplification    : 0.03
% 3.96/1.70  Subsumption          : 0.16
% 3.96/1.70  Abstraction          : 0.04
% 3.96/1.70  MUC search           : 0.00
% 3.96/1.70  Cooper               : 0.00
% 3.96/1.70  Total                : 0.92
% 3.96/1.70  Index Insertion      : 0.00
% 3.96/1.70  Index Deletion       : 0.00
% 3.96/1.70  Index Matching       : 0.00
% 3.96/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
