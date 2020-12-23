%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:47 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 310 expanded)
%              Number of equality atoms :   14 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( r2_hidden(B,C)
                  & r4_lattice3(A,B,C) )
               => k15_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(c_20,plain,(
    k15_lattice3('#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    r4_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v4_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    ! [A_67,B_68,C_69] :
      ( r4_lattice3(A_67,'#skF_2'(A_67,B_68,C_69),B_68)
      | k15_lattice3(A_67,B_68) = C_69
      | ~ r4_lattice3(A_67,C_69,B_68)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ v4_lattice3(A_67)
      | ~ v10_lattices(A_67)
      | ~ l3_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_70,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1('#skF_2'(A_62,B_63,C_64),u1_struct_0(A_62))
      | k15_lattice3(A_62,B_63) = C_64
      | ~ r4_lattice3(A_62,C_64,B_63)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ v4_lattice3(A_62)
      | ~ v10_lattices(A_62)
      | ~ l3_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_39,plain,(
    ! [A_50,D_51,B_52,C_53] :
      ( r1_lattices(A_50,D_51,B_52)
      | ~ r2_hidden(D_51,C_53)
      | ~ m1_subset_1(D_51,u1_struct_0(A_50))
      | ~ r4_lattice3(A_50,B_52,C_53)
      | ~ m1_subset_1(B_52,u1_struct_0(A_50))
      | ~ l3_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ! [A_54,B_55] :
      ( r1_lattices(A_54,'#skF_4',B_55)
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_54))
      | ~ r4_lattice3(A_54,B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l3_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_48,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_3','#skF_4',B_55)
      | ~ r4_lattice3('#skF_3',B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_46])).

tff(c_51,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_3','#skF_4',B_55)
      | ~ r4_lattice3('#skF_3',B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_48])).

tff(c_52,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_3','#skF_4',B_55)
      | ~ r4_lattice3('#skF_3',B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_51])).

tff(c_74,plain,(
    ! [B_63,C_64] :
      ( r1_lattices('#skF_3','#skF_4','#skF_2'('#skF_3',B_63,C_64))
      | ~ r4_lattice3('#skF_3','#skF_2'('#skF_3',B_63,C_64),'#skF_5')
      | k15_lattice3('#skF_3',B_63) = C_64
      | ~ r4_lattice3('#skF_3',C_64,B_63)
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_3'))
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_52])).

tff(c_77,plain,(
    ! [B_63,C_64] :
      ( r1_lattices('#skF_3','#skF_4','#skF_2'('#skF_3',B_63,C_64))
      | ~ r4_lattice3('#skF_3','#skF_2'('#skF_3',B_63,C_64),'#skF_5')
      | k15_lattice3('#skF_3',B_63) = C_64
      | ~ r4_lattice3('#skF_3',C_64,B_63)
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_30,c_74])).

tff(c_78,plain,(
    ! [B_63,C_64] :
      ( r1_lattices('#skF_3','#skF_4','#skF_2'('#skF_3',B_63,C_64))
      | ~ r4_lattice3('#skF_3','#skF_2'('#skF_3',B_63,C_64),'#skF_5')
      | k15_lattice3('#skF_3',B_63) = C_64
      | ~ r4_lattice3('#skF_3',C_64,B_63)
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_77])).

tff(c_84,plain,(
    ! [C_69] :
      ( r1_lattices('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_5',C_69))
      | k15_lattice3('#skF_3','#skF_5') = C_69
      | ~ r4_lattice3('#skF_3',C_69,'#skF_5')
      | ~ m1_subset_1(C_69,u1_struct_0('#skF_3'))
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_78])).

tff(c_87,plain,(
    ! [C_69] :
      ( r1_lattices('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_5',C_69))
      | k15_lattice3('#skF_3','#skF_5') = C_69
      | ~ r4_lattice3('#skF_3',C_69,'#skF_5')
      | ~ m1_subset_1(C_69,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_30,c_84])).

tff(c_89,plain,(
    ! [C_70] :
      ( r1_lattices('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_5',C_70))
      | k15_lattice3('#skF_3','#skF_5') = C_70
      | ~ r4_lattice3('#skF_3',C_70,'#skF_5')
      | ~ m1_subset_1(C_70,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_87])).

tff(c_10,plain,(
    ! [A_23,C_31,B_30] :
      ( ~ r1_lattices(A_23,C_31,'#skF_2'(A_23,B_30,C_31))
      | k15_lattice3(A_23,B_30) = C_31
      | ~ r4_lattice3(A_23,C_31,B_30)
      | ~ m1_subset_1(C_31,u1_struct_0(A_23))
      | ~ v4_lattice3(A_23)
      | ~ v10_lattices(A_23)
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,
    ( ~ v4_lattice3('#skF_3')
    | ~ v10_lattices('#skF_3')
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | k15_lattice3('#skF_3','#skF_5') = '#skF_4'
    | ~ r4_lattice3('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_89,c_10])).

tff(c_96,plain,
    ( v2_struct_0('#skF_3')
    | k15_lattice3('#skF_3','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_28,c_32,c_30,c_93])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_34,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:53:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  %$ r4_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.72/1.17  
% 1.72/1.17  %Foreground sorts:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Background operators:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Foreground operators:
% 1.72/1.17  tff(l3_lattices, type, l3_lattices: $i > $o).
% 1.72/1.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.72/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.17  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 1.72/1.17  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 1.72/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.17  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 1.72/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.72/1.17  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 1.72/1.17  tff(v10_lattices, type, v10_lattices: $i > $o).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.72/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.17  
% 1.72/1.18  tff(f_91, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 1.72/1.18  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 1.72/1.18  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 1.72/1.18  tff(c_20, plain, (k15_lattice3('#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_22, plain, (r4_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_28, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_32, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_30, plain, (v4_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_80, plain, (![A_67, B_68, C_69]: (r4_lattice3(A_67, '#skF_2'(A_67, B_68, C_69), B_68) | k15_lattice3(A_67, B_68)=C_69 | ~r4_lattice3(A_67, C_69, B_68) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~v4_lattice3(A_67) | ~v10_lattices(A_67) | ~l3_lattices(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.72/1.18  tff(c_70, plain, (![A_62, B_63, C_64]: (m1_subset_1('#skF_2'(A_62, B_63, C_64), u1_struct_0(A_62)) | k15_lattice3(A_62, B_63)=C_64 | ~r4_lattice3(A_62, C_64, B_63) | ~m1_subset_1(C_64, u1_struct_0(A_62)) | ~v4_lattice3(A_62) | ~v10_lattices(A_62) | ~l3_lattices(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.72/1.18  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.72/1.18  tff(c_39, plain, (![A_50, D_51, B_52, C_53]: (r1_lattices(A_50, D_51, B_52) | ~r2_hidden(D_51, C_53) | ~m1_subset_1(D_51, u1_struct_0(A_50)) | ~r4_lattice3(A_50, B_52, C_53) | ~m1_subset_1(B_52, u1_struct_0(A_50)) | ~l3_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.18  tff(c_46, plain, (![A_54, B_55]: (r1_lattices(A_54, '#skF_4', B_55) | ~m1_subset_1('#skF_4', u1_struct_0(A_54)) | ~r4_lattice3(A_54, B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l3_lattices(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_24, c_39])).
% 1.72/1.18  tff(c_48, plain, (![B_55]: (r1_lattices('#skF_3', '#skF_4', B_55) | ~r4_lattice3('#skF_3', B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_46])).
% 1.72/1.18  tff(c_51, plain, (![B_55]: (r1_lattices('#skF_3', '#skF_4', B_55) | ~r4_lattice3('#skF_3', B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_48])).
% 1.72/1.18  tff(c_52, plain, (![B_55]: (r1_lattices('#skF_3', '#skF_4', B_55) | ~r4_lattice3('#skF_3', B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_34, c_51])).
% 1.72/1.18  tff(c_74, plain, (![B_63, C_64]: (r1_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3', B_63, C_64)) | ~r4_lattice3('#skF_3', '#skF_2'('#skF_3', B_63, C_64), '#skF_5') | k15_lattice3('#skF_3', B_63)=C_64 | ~r4_lattice3('#skF_3', C_64, B_63) | ~m1_subset_1(C_64, u1_struct_0('#skF_3')) | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_52])).
% 1.72/1.18  tff(c_77, plain, (![B_63, C_64]: (r1_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3', B_63, C_64)) | ~r4_lattice3('#skF_3', '#skF_2'('#skF_3', B_63, C_64), '#skF_5') | k15_lattice3('#skF_3', B_63)=C_64 | ~r4_lattice3('#skF_3', C_64, B_63) | ~m1_subset_1(C_64, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_30, c_74])).
% 1.72/1.18  tff(c_78, plain, (![B_63, C_64]: (r1_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3', B_63, C_64)) | ~r4_lattice3('#skF_3', '#skF_2'('#skF_3', B_63, C_64), '#skF_5') | k15_lattice3('#skF_3', B_63)=C_64 | ~r4_lattice3('#skF_3', C_64, B_63) | ~m1_subset_1(C_64, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_34, c_77])).
% 1.72/1.18  tff(c_84, plain, (![C_69]: (r1_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_5', C_69)) | k15_lattice3('#skF_3', '#skF_5')=C_69 | ~r4_lattice3('#skF_3', C_69, '#skF_5') | ~m1_subset_1(C_69, u1_struct_0('#skF_3')) | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_80, c_78])).
% 1.72/1.18  tff(c_87, plain, (![C_69]: (r1_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_5', C_69)) | k15_lattice3('#skF_3', '#skF_5')=C_69 | ~r4_lattice3('#skF_3', C_69, '#skF_5') | ~m1_subset_1(C_69, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_30, c_84])).
% 1.72/1.18  tff(c_89, plain, (![C_70]: (r1_lattices('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_5', C_70)) | k15_lattice3('#skF_3', '#skF_5')=C_70 | ~r4_lattice3('#skF_3', C_70, '#skF_5') | ~m1_subset_1(C_70, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_34, c_87])).
% 1.72/1.18  tff(c_10, plain, (![A_23, C_31, B_30]: (~r1_lattices(A_23, C_31, '#skF_2'(A_23, B_30, C_31)) | k15_lattice3(A_23, B_30)=C_31 | ~r4_lattice3(A_23, C_31, B_30) | ~m1_subset_1(C_31, u1_struct_0(A_23)) | ~v4_lattice3(A_23) | ~v10_lattices(A_23) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.72/1.18  tff(c_93, plain, (~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3') | k15_lattice3('#skF_3', '#skF_5')='#skF_4' | ~r4_lattice3('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_89, c_10])).
% 1.72/1.18  tff(c_96, plain, (v2_struct_0('#skF_3') | k15_lattice3('#skF_3', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_28, c_32, c_30, c_93])).
% 1.72/1.18  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_34, c_96])).
% 1.72/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  Inference rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Ref     : 0
% 1.72/1.18  #Sup     : 8
% 1.72/1.18  #Fact    : 0
% 1.72/1.18  #Define  : 0
% 1.72/1.18  #Split   : 0
% 1.72/1.18  #Chain   : 0
% 1.72/1.18  #Close   : 0
% 1.72/1.18  
% 1.72/1.18  Ordering : KBO
% 1.72/1.18  
% 1.72/1.18  Simplification rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Subsume      : 0
% 1.72/1.18  #Demod        : 14
% 1.72/1.18  #Tautology    : 0
% 1.72/1.18  #SimpNegUnit  : 5
% 1.72/1.18  #BackRed      : 0
% 1.72/1.18  
% 1.72/1.18  #Partial instantiations: 0
% 1.72/1.18  #Strategies tried      : 1
% 1.72/1.18  
% 1.72/1.18  Timing (in seconds)
% 1.72/1.18  ----------------------
% 1.99/1.18  Preprocessing        : 0.27
% 1.99/1.18  Parsing              : 0.14
% 1.99/1.18  CNF conversion       : 0.02
% 1.99/1.18  Main loop            : 0.15
% 1.99/1.18  Inferencing          : 0.07
% 1.99/1.18  Reduction            : 0.04
% 1.99/1.18  Demodulation         : 0.03
% 1.99/1.18  BG Simplification    : 0.02
% 1.99/1.18  Subsumption          : 0.03
% 1.99/1.18  Abstraction          : 0.01
% 1.99/1.18  MUC search           : 0.00
% 1.99/1.18  Cooper               : 0.00
% 1.99/1.18  Total                : 0.46
% 1.99/1.18  Index Insertion      : 0.00
% 1.99/1.18  Index Deletion       : 0.00
% 1.99/1.18  Index Matching       : 0.00
% 1.99/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
