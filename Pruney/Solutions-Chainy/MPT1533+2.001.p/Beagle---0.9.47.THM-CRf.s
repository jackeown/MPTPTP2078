%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:59 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   42 (  65 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 220 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r2_hidden > m1_subset_1 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( ( r2_lattice3(A,B,C)
                    & r1_orders_2(A,C,D) )
                 => r2_lattice3(A,B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(c_16,plain,(
    r2_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_16,B_23,C_24] :
      ( m1_subset_1('#skF_1'(A_16,B_23,C_24),u1_struct_0(A_16))
      | r2_lattice3(A_16,B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_16,B_23,C_24] :
      ( r2_hidden('#skF_1'(A_16,B_23,C_24),B_23)
      | r2_lattice3(A_16,B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_42,D_43,C_44,B_45] :
      ( r1_orders_2(A_42,D_43,C_44)
      | ~ r2_hidden(D_43,B_45)
      | ~ m1_subset_1(D_43,u1_struct_0(A_42))
      | ~ r2_lattice3(A_42,B_45,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_42))
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    ! [A_53,C_51,A_52,C_55,B_54] :
      ( r1_orders_2(A_52,'#skF_1'(A_53,B_54,C_51),C_55)
      | ~ m1_subset_1('#skF_1'(A_53,B_54,C_51),u1_struct_0(A_52))
      | ~ r2_lattice3(A_52,B_54,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(A_52))
      | ~ l1_orders_2(A_52)
      | r2_lattice3(A_53,B_54,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_8,c_28])).

tff(c_74,plain,(
    ! [A_59,B_60,C_61,C_62] :
      ( r1_orders_2(A_59,'#skF_1'(A_59,B_60,C_61),C_62)
      | ~ r2_lattice3(A_59,B_60,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_59))
      | r2_lattice3(A_59,B_60,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59) ) ),
    inference(resolution,[status(thm)],[c_10,c_56])).

tff(c_24,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_46,B_47,D_48,C_49] :
      ( r1_orders_2(A_46,B_47,D_48)
      | ~ r1_orders_2(A_46,C_49,D_48)
      | ~ r1_orders_2(A_46,B_47,C_49)
      | ~ m1_subset_1(D_48,u1_struct_0(A_46))
      | ~ m1_subset_1(C_49,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46)
      | ~ v4_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [B_47] :
      ( r1_orders_2('#skF_2',B_47,'#skF_5')
      | ~ r1_orders_2('#skF_2',B_47,'#skF_4')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_32])).

tff(c_38,plain,(
    ! [B_50] :
      ( r1_orders_2('#skF_2',B_50,'#skF_5')
      | ~ r1_orders_2('#skF_2',B_50,'#skF_4')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_34])).

tff(c_42,plain,(
    ! [B_23,C_24] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_23,C_24),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_23,C_24),'#skF_4')
      | r2_lattice3('#skF_2',B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_38])).

tff(c_60,plain,(
    ! [B_56,C_57] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_56,C_57),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_56,C_57),'#skF_4')
      | r2_lattice3('#skF_2',B_56,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_6,plain,(
    ! [A_16,B_23,C_24] :
      ( ~ r1_orders_2(A_16,'#skF_1'(A_16,B_23,C_24),C_24)
      | r2_lattice3(A_16,B_23,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [B_56] :
      ( ~ l1_orders_2('#skF_2')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_56,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_2',B_56,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_60,c_6])).

tff(c_72,plain,(
    ! [B_56] :
      ( ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_56,'#skF_5'),'#skF_4')
      | r2_lattice3('#skF_2',B_56,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22,c_66])).

tff(c_78,plain,(
    ! [B_60] :
      ( ~ r2_lattice3('#skF_2',B_60,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | r2_lattice3('#skF_2',B_60,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_72])).

tff(c_97,plain,(
    ! [B_66] :
      ( ~ r2_lattice3('#skF_2',B_66,'#skF_4')
      | r2_lattice3('#skF_2',B_66,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_20,c_78])).

tff(c_12,plain,(
    ~ r2_lattice3('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_100,plain,(
    ~ r2_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_12])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:33:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.11  
% 1.83/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.11  %$ r2_lattice3 > r1_orders_2 > r2_hidden > m1_subset_1 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.83/1.11  
% 1.83/1.11  %Foreground sorts:
% 1.83/1.11  
% 1.83/1.11  
% 1.83/1.11  %Background operators:
% 1.83/1.11  
% 1.83/1.11  
% 1.83/1.11  %Foreground operators:
% 1.83/1.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.83/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.11  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.83/1.11  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.83/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.83/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.11  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.83/1.11  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.83/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.83/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.11  
% 1.83/1.13  tff(f_75, negated_conjecture, ~(![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_lattice3(A, B, C) & r1_orders_2(A, C, D)) => r2_lattice3(A, B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_yellow_0)).
% 1.83/1.13  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 1.83/1.13  tff(f_44, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 1.83/1.13  tff(c_16, plain, (r2_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.83/1.13  tff(c_22, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.83/1.13  tff(c_18, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.83/1.13  tff(c_20, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.83/1.13  tff(c_10, plain, (![A_16, B_23, C_24]: (m1_subset_1('#skF_1'(A_16, B_23, C_24), u1_struct_0(A_16)) | r2_lattice3(A_16, B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.83/1.13  tff(c_8, plain, (![A_16, B_23, C_24]: (r2_hidden('#skF_1'(A_16, B_23, C_24), B_23) | r2_lattice3(A_16, B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.83/1.13  tff(c_28, plain, (![A_42, D_43, C_44, B_45]: (r1_orders_2(A_42, D_43, C_44) | ~r2_hidden(D_43, B_45) | ~m1_subset_1(D_43, u1_struct_0(A_42)) | ~r2_lattice3(A_42, B_45, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_42)) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.83/1.13  tff(c_56, plain, (![A_53, C_51, A_52, C_55, B_54]: (r1_orders_2(A_52, '#skF_1'(A_53, B_54, C_51), C_55) | ~m1_subset_1('#skF_1'(A_53, B_54, C_51), u1_struct_0(A_52)) | ~r2_lattice3(A_52, B_54, C_55) | ~m1_subset_1(C_55, u1_struct_0(A_52)) | ~l1_orders_2(A_52) | r2_lattice3(A_53, B_54, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_53)) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_8, c_28])).
% 1.83/1.13  tff(c_74, plain, (![A_59, B_60, C_61, C_62]: (r1_orders_2(A_59, '#skF_1'(A_59, B_60, C_61), C_62) | ~r2_lattice3(A_59, B_60, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_59)) | r2_lattice3(A_59, B_60, C_61) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~l1_orders_2(A_59))), inference(resolution, [status(thm)], [c_10, c_56])).
% 1.83/1.13  tff(c_24, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.83/1.13  tff(c_14, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.83/1.13  tff(c_32, plain, (![A_46, B_47, D_48, C_49]: (r1_orders_2(A_46, B_47, D_48) | ~r1_orders_2(A_46, C_49, D_48) | ~r1_orders_2(A_46, B_47, C_49) | ~m1_subset_1(D_48, u1_struct_0(A_46)) | ~m1_subset_1(C_49, u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_orders_2(A_46) | ~v4_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.13  tff(c_34, plain, (![B_47]: (r1_orders_2('#skF_2', B_47, '#skF_5') | ~r1_orders_2('#skF_2', B_47, '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(B_47, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v4_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_32])).
% 1.83/1.13  tff(c_38, plain, (![B_50]: (r1_orders_2('#skF_2', B_50, '#skF_5') | ~r1_orders_2('#skF_2', B_50, '#skF_4') | ~m1_subset_1(B_50, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_34])).
% 1.83/1.13  tff(c_42, plain, (![B_23, C_24]: (r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_23, C_24), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_23, C_24), '#skF_4') | r2_lattice3('#skF_2', B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_38])).
% 1.83/1.13  tff(c_60, plain, (![B_56, C_57]: (r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_56, C_57), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_56, C_57), '#skF_4') | r2_lattice3('#skF_2', B_56, C_57) | ~m1_subset_1(C_57, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_42])).
% 1.83/1.13  tff(c_6, plain, (![A_16, B_23, C_24]: (~r1_orders_2(A_16, '#skF_1'(A_16, B_23, C_24), C_24) | r2_lattice3(A_16, B_23, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.83/1.13  tff(c_66, plain, (![B_56]: (~l1_orders_2('#skF_2') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_56, '#skF_5'), '#skF_4') | r2_lattice3('#skF_2', B_56, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_60, c_6])).
% 1.83/1.13  tff(c_72, plain, (![B_56]: (~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_56, '#skF_5'), '#skF_4') | r2_lattice3('#skF_2', B_56, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22, c_66])).
% 1.83/1.13  tff(c_78, plain, (![B_60]: (~r2_lattice3('#skF_2', B_60, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | r2_lattice3('#skF_2', B_60, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_72])).
% 1.83/1.13  tff(c_97, plain, (![B_66]: (~r2_lattice3('#skF_2', B_66, '#skF_4') | r2_lattice3('#skF_2', B_66, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_20, c_78])).
% 1.83/1.13  tff(c_12, plain, (~r2_lattice3('#skF_2', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.83/1.13  tff(c_100, plain, (~r2_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_97, c_12])).
% 1.83/1.13  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_100])).
% 1.83/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.13  
% 1.83/1.13  Inference rules
% 1.83/1.13  ----------------------
% 1.83/1.13  #Ref     : 0
% 1.83/1.13  #Sup     : 13
% 1.83/1.13  #Fact    : 0
% 1.83/1.13  #Define  : 0
% 1.83/1.13  #Split   : 1
% 1.83/1.13  #Chain   : 0
% 1.83/1.13  #Close   : 0
% 1.83/1.13  
% 1.83/1.13  Ordering : KBO
% 1.83/1.13  
% 1.83/1.13  Simplification rules
% 1.83/1.13  ----------------------
% 1.83/1.13  #Subsume      : 0
% 1.83/1.13  #Demod        : 16
% 1.83/1.13  #Tautology    : 2
% 1.83/1.13  #SimpNegUnit  : 0
% 1.83/1.13  #BackRed      : 0
% 1.83/1.13  
% 1.83/1.13  #Partial instantiations: 0
% 1.83/1.13  #Strategies tried      : 1
% 1.83/1.13  
% 1.83/1.13  Timing (in seconds)
% 1.83/1.13  ----------------------
% 1.83/1.13  Preprocessing        : 0.28
% 1.83/1.13  Parsing              : 0.16
% 1.83/1.13  CNF conversion       : 0.02
% 1.83/1.13  Main loop            : 0.15
% 1.83/1.13  Inferencing          : 0.07
% 1.83/1.13  Reduction            : 0.04
% 1.83/1.13  Demodulation         : 0.03
% 1.83/1.13  BG Simplification    : 0.01
% 1.83/1.13  Subsumption          : 0.03
% 1.83/1.13  Abstraction          : 0.01
% 1.83/1.13  MUC search           : 0.00
% 1.83/1.13  Cooper               : 0.00
% 1.83/1.13  Total                : 0.46
% 1.83/1.13  Index Insertion      : 0.00
% 1.83/1.13  Index Deletion       : 0.00
% 1.83/1.13  Index Matching       : 0.00
% 1.83/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
